structure Sha256 :> SHA256 =
struct
  structure W    = Word
  structure W8   = Word8
  structure W32  = Word32
  structure W8V  = Word8Vector
  structure W8VS = Word8VectorSlice

  val k : W32.word vector =
    Vector.fromList [0wx428A2F98, 0wx71374491, 0wxB5C0FBCF, 0wxE9B5DBA5,
                     0wx3956C25B, 0wx59F111F1, 0wx923F82A4, 0wxAB1C5ED5,
                     0wxD807AA98, 0wx12835B01, 0wx243185BE, 0wx550C7DC3,
                     0wx72BE5D74, 0wx80DEB1FE, 0wx9BDC06A7, 0wxC19BF174,
                     0wxE49B69C1, 0wxEFBE4786, 0wx0FC19DC6, 0wx240CA1CC,
                     0wx2DE92C6F, 0wx4A7484AA, 0wx5CB0A9DC, 0wx76F988DA,
                     0wx983E5152, 0wxA831C66D, 0wxB00327C8, 0wxBF597FC7,
                     0wxC6E00BF3, 0wxD5A79147, 0wx06CA6351, 0wx14292967,
                     0wx27B70A85, 0wx2E1B2138, 0wx4D2C6DFC, 0wx53380D13,
                     0wx650A7354, 0wx766A0ABB, 0wx81C2C92E, 0wx92722C85,
                     0wxA2BFE8A1, 0wxA81A664B, 0wxC24B8B70, 0wxC76C51A3,
                     0wxD192E819, 0wxD6990624, 0wxF40E3585, 0wx106AA070,
                     0wx19A4C116, 0wx1E376C08, 0wx2748774C, 0wx34B0BCB5,
                     0wx391C0CB3, 0wx4ED8AA4A, 0wx5B9CCA4F, 0wx682E6FF3,
                     0wx748F82EE, 0wx78A5636F, 0wx84C87814, 0wx8CC70208,
                     0wx90BEFFFA, 0wxA4506CEB, 0wxBEF9A3F7, 0wxC67178F2]

  val h0 : W32.word vector =
    Vector.fromList [0wx6A09E667, 0wxBB67AE85, 0wx3C6EF372, 0wxA54FF53A,
                     0wx510E527F, 0wx9B05688C, 0wx1F83D9AB, 0wx5BE0CD19]

  val op ++ = W32.+
  val op >> = W32.>>
  val op << = W32.<<
  val andb  = W32.andb
  val orb   = W32.orb
  val xorb  = W32.xorb
  val notb  = W32.notb

  infix 6 ++
  infix 5 << >>
  infix 4 andb
  infix 3 xorb orb

  fun toW8  w32 = W8.fromInt (W32.toInt w32)
  fun toW32 w8  = W32.fromInt (W8.toInt w8)

  fun rotr (x, n) = (x >> W.fromInt n) orb (x << W.fromInt (32 - n))
  fun shr  (x, n) = x >> W.fromInt n
  fun shl  (x, n) = x << W.fromInt n

  fun ch  (x, y, z) = (x andb y) xorb (notb x andb z)
  fun maj (x, y, z) = (x andb y) xorb (x andb z) xorb (y andb z)

  fun usig0 x = rotr (x, 2)  xorb rotr (x, 13) xorb rotr (x, 22)
  fun usig1 x = rotr (x, 6)  xorb rotr (x, 11) xorb rotr (x, 25)
  fun lsig0 x = rotr (x, 7)  xorb rotr (x, 18) xorb shr (x, 3)
  fun lsig1 x = rotr (x, 17) xorb rotr (x, 19) xorb shr (x, 10)

  fun pad (msg : W8V.vector) : W8V.vector =
    let
      val l = W8V.length msg * 8
      val k = (448 - l - 1) mod 512
      val xs = W8V.fromList (0wx80::List.tabulate (k div 8, fn _ => 0wx00))
      val ys =
        let
          val l' = W32.fromInt l
          fun f i = toW8 (l' >> W.fromInt (56 - i * 8) andb 0wx000000FF)
        in
          W8V.tabulate (8, f)
        end
    in
      W8V.concat [msg, xs, ys]
    end


  fun parse (msg : W8V.vector) : W32.word vector vector =
    let
      val l = W8V.length msg
      fun convert w8v =
        let
          val n = W8V.length w8v
        in
          Vector.tabulate
            (n div 4,
             fn i => (toW32 (W8V.sub (w8v, i * 4 + 0)) << 0w24) ++
                     (toW32 (W8V.sub (w8v, i * 4 + 1)) << 0w16) ++
                     (toW32 (W8V.sub (w8v, i * 4 + 2)) << 0w08) ++
                     (toW32 (W8V.sub (w8v, i * 4 + 3)) << 0w00))
        end
    in
      Vector.map convert
                 (Vector.tabulate (l div 64,
                                   fn i => W8VS.vector (W8VS.slice (msg, i * 64, SOME 64))))
    end

  fun hashOneStep (msg, h) : W32.word vector =
    let
      val msgSched = Array.array (64, 0w0)
      val a0 = ref (Vector.sub (h, 0))
      val a1 = ref (Vector.sub (h, 1))
      val a2 = ref (Vector.sub (h, 2))
      val a3 = ref (Vector.sub (h, 3))
      val a4 = ref (Vector.sub (h, 4))
      val a5 = ref (Vector.sub (h, 5))
      val a6 = ref (Vector.sub (h, 6))
      val a7 = ref (Vector.sub (h, 7))

      fun calcMsgSched () =
        let
          val t = ref 0
        in
          while !t < 64 do (
            if !t <= 15 then
              Array.update (msgSched, !t, Vector.sub (msg, !t))
            else
              let
                val w1 = lsig1 (Array.sub (msgSched, !t - 2))
                val w2 = Array.sub (msgSched, !t - 7)
                val w3 = lsig0 (Array.sub (msgSched, !t - 15))
                val w4 = Array.sub (msgSched, !t - 16)
              in
                Array.update (msgSched, !t, w1 ++ w2 ++ w3 ++ w4)
              end;
            t := !t + 1)
        end

      fun calcWorks () =
        let
          val tmp1 = ref 0w0
          val tmp2 = ref 0w0
          val t     = ref 0
        in
          while !t < 64 do (
            tmp1 := !a7 ++ usig1 (!a4) ++ ch (!a4, !a5, !a6) ++
                     Vector.sub (k, !t) ++ Array.sub (msgSched, !t);
            tmp2 := usig0 (!a0) ++ maj (!a0, !a1, !a2);
            a7 := !a6;
            a6 := !a5;
            a5 := !a4;
            a4 := !a3 ++ !tmp1;
            a3 := !a2;
            a2 := !a1;
            a1 := !a0;
            a0 := !tmp1 ++ !tmp2;
            t  := !t + 1)
        end
    in
      calcMsgSched ();
      calcWorks ();
      Vector.fromList [!a0 ++ Vector.sub (h, 0),
                       !a1 ++ Vector.sub (h, 1),
                       !a2 ++ Vector.sub (h, 2),
                       !a3 ++ Vector.sub (h, 3),
                       !a4 ++ Vector.sub (h, 4),
                       !a5 ++ Vector.sub (h, 5),
                       !a6 ++ Vector.sub (h, 6),
                       !a7 ++ Vector.sub (h, 7)]
    end

  fun hash (msg : W8V.vector) : W32.word vector =
    let
      val msgs = parse (pad msg)
      val n = Vector.length msgs
      val i = ref 0
      val h = ref h0
    in
      while !i < n do (
        h := hashOneStep (Vector.sub (msgs, !i), !h);
        i := !i + 1);
      !h
    end

  fun hashW8 msg =
    let
      val h = hash msg
      val n = Vector.length h
      fun f i =
        let
          val q   = i div 4
          val r   = i mod 4
          val w32 = Vector.sub (h, q)
        in
          toW8 (w32 >> W.fromInt (24 - r * 8) andb 0wx000000FF)
        end
    in
      W8V.tabulate (n * 4, f)
    end
end
