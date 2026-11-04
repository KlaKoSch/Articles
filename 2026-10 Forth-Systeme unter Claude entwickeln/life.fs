\ Conway's Game of Life, 25x25, Ränder laufen um (Torus)
\
\ Start:   ./forth life.fs
\ Danach:  clear glider 60 run
\          clear rpent 200 run

25 constant w
25 constant h
w h * constant size

create grid size allot        \ aktuelle Generation (0 = tot, 1 = lebt)
create next size allot        \ Puffer für die nächste Generation

variable cx
variable cy

\ ---------- Feldzugriff ----------

: idx ( x y -- i )   w * + ;

: wrapx ( x -- x' )  w + w mod ;
: wrapy ( y -- y' )  h + h mod ;

: at ( x y -- n )    wrapy swap wrapx swap idx grid + @ ;

: set ( x y -- )     idx grid + 1 swap ! ;

: clear ( -- )       size 0 do 0 grid i + ! loop ;

: population ( -- n ) 0 size 0 do grid i + @ + loop ;

\ ---------- Spielregeln ----------

: n@ ( dx dy -- n )  cy @ + swap cx @ + swap at ;

: neighbors ( x y -- n )
  cy ! cx !
  -1 -1 n@   0 -1 n@ +   1 -1 n@ +
  -1  0 n@ +             1  0 n@ +
  -1  1 n@ + 0  1 n@ +   1  1 n@ + ;

\ lebende Zelle: bei 2 oder 3 Nachbarn weiter, tote Zelle: bei 3 Nachbarn neu
: rule ( alive n -- 0|1 )
  over if
    dup 2 = swap 3 = or
  else
    3 =
  then
  nip negate ;

: step ( -- )
  h 0 do
    w 0 do
      i j at  i j neighbors  rule
      i j idx next + !
    loop
  loop ;

: commit ( -- )      size 0 do next i + @ grid i + ! loop ;

: generation ( -- )  step commit ;

\ ---------- Anzeige ----------

: show ( -- )
  h 0 do
    w 0 do
      i j at if ." # " else ." . " then
    loop
    cr
  loop ;

: run ( n -- )
  0 do
    page
    ." Generation " i . ."  Zellen: " population . cr
    show
    generation
    120 ms
  loop ;

\ ---------- Startmuster ----------

: glider ( -- )   1 0 set  2 1 set  0 2 set  1 2 set  2 2 set ;
: blinker ( -- )  11 12 set  12 12 set  13 12 set ;
: rpent ( -- )    12 11 set  13 11 set  11 12 set  12 12 set  12 13 set ;

." Life geladen. Beispiel:  clear glider 60 run" cr
