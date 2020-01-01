structure Sha1 :> SHA =
struct
  structure W    = Word
  structure W8   = Word8
  structure W32  = Word32
  structure W8V  = Word8Vector
  structure W8VS = Word8VectorSlice

  val k : int -> W32.word =
   fn t => if t >= 0 andalso t < 20 then 0wx5A827999
           else if t >= 20 andalso t < 40 then 0wx6ED9EBA1
           else if t >= 40 andalso t < 60 then 0wx8F1BBCDC
           else 0wxCA62C1D6

  val h0 : W32.word vector =
    Vector.fromList [0wx67452301,
                     0wxEFCDAB89,
                     0wx98BADCFE,
                     0wx10325476,
                     0wxC3D2E1F0]

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
  fun rotl (x, n) = (x << W.fromInt n) orb (x >> W.fromInt (32 - n))

  fun ch     (x, y, z) = (x andb y) xorb (notb x andb z)
  fun parity (x, y, z) = x xorb y xorb z
  fun maj    (x, y, z) = (x andb y) xorb (x andb z) xorb (y andb z)

  val f =
   fn t => if t >= 0 andalso t < 20 then ch
           else if t >= 20 andalso t < 40 then parity
           else if t >= 40 andalso t < 60 then maj
           else parity

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
      val msgSched = Array.array (80, 0w0)
      val a0 = ref (Vector.sub (h, 0))
      val a1 = ref (Vector.sub (h, 1))
      val a2 = ref (Vector.sub (h, 2))
      val a3 = ref (Vector.sub (h, 3))
      val a4 = ref (Vector.sub (h, 4))

      fun calcMsgSched () =
        let
          val t = ref 0
        in
          while !t < 80 do (
            if !t <= 15 then
              Array.update (msgSched, !t, Vector.sub (msg, !t))
            else
              let
                val w1 = Array.sub (msgSched, !t - 3)
                val w2 = Array.sub (msgSched, !t - 8)
                val w3 = Array.sub (msgSched, !t - 14)
                val w4 = Array.sub (msgSched, !t - 16)
              in
                Array.update (msgSched, !t, rotl (w1 xorb w2 xorb w3 xorb w4, 1))
              end;
            t := !t + 1)
        end

      fun calcWorks () =
        let
          val tmp = ref 0w0
          val t   = ref 0
        in
          while !t < 80 do (
            tmp := rotl (!a0, 5) ++ f (!t) (!a1, !a2, !a3) ++
                   !a4 ++ k (!t) ++ Array.sub (msgSched, !t);
            a4 := !a3;
            a3 := !a2;
            a2 := rotl (!a1, 30);
            a1 := !a0;
            a0 := !tmp;
            t  := !t + 1)
        end
    in
      calcMsgSched ();
      calcWorks ();
      Vector.fromList [!a0 ++ Vector.sub (h, 0),
                       !a1 ++ Vector.sub (h, 1),
                       !a2 ++ Vector.sub (h, 2),
                       !a3 ++ Vector.sub (h, 3),
                       !a4 ++ Vector.sub (h, 4)]
    end

  fun hash (msg : W8V.vector) : W32.word vector =
    let
      val msgs = parse (pad msg)
    in
      Vector.foldl hashOneStep h0 msgs
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
