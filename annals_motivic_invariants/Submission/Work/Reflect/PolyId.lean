import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.CharP.Defs

/-!
# Polynomial identities by reflection

`refl_ring1` proves an equality `A = B` in a commutative ring by reifying both sides into
`Lean.Grind.CommRing.Expr` and checking, by kernel computation, that the sparse normal form of
`A - B` is zero.  The proof term is linear in the size of the goal, instead of the full
normalisation trace that `ring` produces.

The normaliser is written for the kernel: functions are defined directly by recursors, a
monomial `∏ xᵢ ^ eᵢ` is encoded as the natural number `∏ pᵢ ^ eᵢ` (`pᵢ` the `i`-th prime), so that
monomial multiplication, comparison and equality are single GMP-accelerated `Nat` operations, and
products are summed by balanced pairwise merging.

Use it as the normaliser of `linear_combination`:
`linear_combination (norm := refl_ring1) e`.
-/

set_option maxRecDepth 100000

namespace Work.Reflect

open Lean.Grind.CommRing (Expr Context)

/-- Sparse polynomials: coefficient, monomial code, rest (sorted by decreasing code). -/
inductive P where
  | nil
  | cons (c : Int) (m : Nat) (p : P)

/-- Identity, as a named definition.  Wrapping a non-productive recursive result in it makes the
next reduction step a delta-unfolding, which keeps the reduction iterative in kernels whose
`whnf` only loops on delta steps (nanoda), instead of growing the stack per iota step. -/
def idP (p : P) : P := p
/-- `Bool` version of `idP`. -/
def idB (b : Bool) : Bool := b
/-- `List P` version of `idP`. -/
def idL (l : List P) : List P := l

/-- Coefficient normalisation modulo `md` (`md = 0`: no reduction). -/
noncomputable def cn (md : Nat) (c : Int) : Int := Int.emod c (Int.ofNat md)

/-- Merge two polynomials (sorted by decreasing monomial code), adding coefficients of equal
monomials.  Nested recursion: outer on `p`, inner on `q`. -/
noncomputable def padd (md : Nat) : P → P → P :=
  fun p => P.rec (motive := fun _ => P → P) (fun q => q)
    (fun c m p' ih => fun q =>
      P.rec (motive := fun _ => P) (.cons c m p')
        (fun d n q' ihq =>
          Bool.rec
            (Bool.rec (.cons c m (ih (.cons d n q'))) (.cons d n ihq) (Nat.ble m n))
            (Bool.rec (.cons (cn md (Int.add c d)) m (ih q')) (idP (ih q'))
              (Int.beq' (cn md (Int.add c d)) 0))
            (Nat.beq m n))
        q)
    p

noncomputable def pmulT (md : Nat) (c : Int) (m : Nat) (q : P) : P :=
  P.rec (motive := fun _ => P) .nil
    (fun d n _ ih => Bool.rec (.cons (cn md (Int.mul c d)) (Nat.mul m n) ih) (idP ih)
      (Int.beq' (cn md (Int.mul c d)) 0)) q

noncomputable def pneg (md : Nat) (q : P) : P :=
  P.rec (motive := fun _ => P) .nil (fun d n _ ih => .cons (cn md (Int.neg d)) n ih) q

noncomputable def plen (q : P) : Nat :=
  P.rec (motive := fun _ => Nat) 0 (fun _ _ _ ih => Nat.add ih 1) q

/-- `[t * q | t ∈ p]` -/
noncomputable def termsOf (md : Nat) (q p : P) : List P :=
  P.rec (motive := fun _ => List P) [] (fun c m _ ih => pmulT md c m q :: ih) p

noncomputable def pairUp (md : Nat) : List P → List P
  | a :: b :: rest => padd md a b :: pairUp md rest
  | l => l

noncomputable def sumAll (md : Nat) : Nat → List P → P
  | 0, l => l.foldr (padd md) .nil
  | _ + 1, [] => .nil
  | _ + 1, [a] => a
  | n + 1, a :: b :: l => sumAll md n (pairUp md (a :: b :: l))

/-- Product; iterates over the shorter factor. -/
noncomputable def pmul (md : Nat) (p q : P) : P :=
  Bool.rec (sumAll md 64 (termsOf md p q)) (sumAll md 64 (termsOf md q p))
    (Nat.ble (plen p) (plen q))

noncomputable def ppow (md : Nat) (p : P) (k : Nat) : P :=
  Nat.rec (motive := fun _ => P) (.cons 1 1 .nil) (fun _ ih => pmul md ih p) k

noncomputable def pconst (md : Nat) (k : Int) : P :=
  Bool.rec (.cons (cn md k) 1 .nil) .nil (Int.beq' (cn md k) 0)

/-- The same primes as a balanced binary tree, for O(log n) kernel lookup. -/
def primeArr : Lean.RArray Nat :=
  (.branch 1024 (.branch 512 (.branch 256 (.branch 128 (.branch 64 (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 2) (.leaf 3)) (.branch 3 (.leaf 5) (.leaf 7))) (.branch 6
  (.branch 5 (.leaf 11) (.leaf 13)) (.branch 7 (.leaf 17) (.leaf 19)))) (.branch 12 (.branch 10
  (.branch 9 (.leaf 23) (.leaf 29)) (.branch 11 (.leaf 31) (.leaf 37))) (.branch 14 (.branch 13
  (.leaf 41) (.leaf 43)) (.branch 15 (.leaf 47) (.leaf 53))))) (.branch 24 (.branch 20 (.branch 18
  (.branch 17 (.leaf 59) (.leaf 61)) (.branch 19 (.leaf 67) (.leaf 71))) (.branch 22 (.branch 21
  (.leaf 73) (.leaf 79)) (.branch 23 (.leaf 83) (.leaf 89)))) (.branch 28 (.branch 26 (.branch 25
  (.leaf 97) (.leaf 101)) (.branch 27 (.leaf 103) (.leaf 107))) (.branch 30 (.branch 29 (.leaf 109)
  (.leaf 113)) (.branch 31 (.leaf 127) (.leaf 131)))))) (.branch 48 (.branch 40 (.branch 36 (.branch
  34 (.branch 33 (.leaf 137) (.leaf 139)) (.branch 35 (.leaf 149) (.leaf 151))) (.branch 38 (.branch
  37 (.leaf 157) (.leaf 163)) (.branch 39 (.leaf 167) (.leaf 173)))) (.branch 44 (.branch 42 (.branch
  41 (.leaf 179) (.leaf 181)) (.branch 43 (.leaf 191) (.leaf 193))) (.branch 46 (.branch 45 (.leaf
  197) (.leaf 199)) (.branch 47 (.leaf 211) (.leaf 223))))) (.branch 56 (.branch 52 (.branch 50
  (.branch 49 (.leaf 227) (.leaf 229)) (.branch 51 (.leaf 233) (.leaf 239))) (.branch 54 (.branch 53
  (.leaf 241) (.leaf 251)) (.branch 55 (.leaf 257) (.leaf 263)))) (.branch 60 (.branch 58 (.branch 57
  (.leaf 269) (.leaf 271)) (.branch 59 (.leaf 277) (.leaf 281))) (.branch 62 (.branch 61 (.leaf 283)
  (.leaf 293)) (.branch 63 (.leaf 307) (.leaf 311))))))) (.branch 96 (.branch 80 (.branch 72 (.branch
  68 (.branch 66 (.branch 65 (.leaf 313) (.leaf 317)) (.branch 67 (.leaf 331) (.leaf 337))) (.branch
  70 (.branch 69 (.leaf 347) (.leaf 349)) (.branch 71 (.leaf 353) (.leaf 359)))) (.branch 76 (.branch
  74 (.branch 73 (.leaf 367) (.leaf 373)) (.branch 75 (.leaf 379) (.leaf 383))) (.branch 78 (.branch
  77 (.leaf 389) (.leaf 397)) (.branch 79 (.leaf 401) (.leaf 409))))) (.branch 88 (.branch 84
  (.branch 82 (.branch 81 (.leaf 419) (.leaf 421)) (.branch 83 (.leaf 431) (.leaf 433))) (.branch 86
  (.branch 85 (.leaf 439) (.leaf 443)) (.branch 87 (.leaf 449) (.leaf 457)))) (.branch 92 (.branch 90
  (.branch 89 (.leaf 461) (.leaf 463)) (.branch 91 (.leaf 467) (.leaf 479))) (.branch 94 (.branch 93
  (.leaf 487) (.leaf 491)) (.branch 95 (.leaf 499) (.leaf 503)))))) (.branch 112 (.branch 104
  (.branch 100 (.branch 98 (.branch 97 (.leaf 509) (.leaf 521)) (.branch 99 (.leaf 523) (.leaf 541)))
  (.branch 102 (.branch 101 (.leaf 547) (.leaf 557)) (.branch 103 (.leaf 563) (.leaf 569)))) (.branch
  108 (.branch 106 (.branch 105 (.leaf 571) (.leaf 577)) (.branch 107 (.leaf 587) (.leaf 593)))
  (.branch 110 (.branch 109 (.leaf 599) (.leaf 601)) (.branch 111 (.leaf 607) (.leaf 613)))))
  (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf 617) (.leaf 619)) (.branch 115 (.leaf
  631) (.leaf 641))) (.branch 118 (.branch 117 (.leaf 643) (.leaf 647)) (.branch 119 (.leaf 653)
  (.leaf 659)))) (.branch 124 (.branch 122 (.branch 121 (.leaf 661) (.leaf 673)) (.branch 123 (.leaf
  677) (.leaf 683))) (.branch 126 (.branch 125 (.leaf 691) (.leaf 701)) (.branch 127 (.leaf 709)
  (.leaf 719)))))))) (.branch 192 (.branch 160 (.branch 144 (.branch 136 (.branch 132 (.branch 130
  (.branch 129 (.leaf 727) (.leaf 733)) (.branch 131 (.leaf 739) (.leaf 743))) (.branch 134 (.branch
  133 (.leaf 751) (.leaf 757)) (.branch 135 (.leaf 761) (.leaf 769)))) (.branch 140 (.branch 138
  (.branch 137 (.leaf 773) (.leaf 787)) (.branch 139 (.leaf 797) (.leaf 809))) (.branch 142 (.branch
  141 (.leaf 811) (.leaf 821)) (.branch 143 (.leaf 823) (.leaf 827))))) (.branch 152 (.branch 148
  (.branch 146 (.branch 145 (.leaf 829) (.leaf 839)) (.branch 147 (.leaf 853) (.leaf 857))) (.branch
  150 (.branch 149 (.leaf 859) (.leaf 863)) (.branch 151 (.leaf 877) (.leaf 881)))) (.branch 156
  (.branch 154 (.branch 153 (.leaf 883) (.leaf 887)) (.branch 155 (.leaf 907) (.leaf 911))) (.branch
  158 (.branch 157 (.leaf 919) (.leaf 929)) (.branch 159 (.leaf 937) (.leaf 941)))))) (.branch 176
  (.branch 168 (.branch 164 (.branch 162 (.branch 161 (.leaf 947) (.leaf 953)) (.branch 163 (.leaf
  967) (.leaf 971))) (.branch 166 (.branch 165 (.leaf 977) (.leaf 983)) (.branch 167 (.leaf 991)
  (.leaf 997)))) (.branch 172 (.branch 170 (.branch 169 (.leaf 1009) (.leaf 1013)) (.branch 171
  (.leaf 1019) (.leaf 1021))) (.branch 174 (.branch 173 (.leaf 1031) (.leaf 1033)) (.branch 175
  (.leaf 1039) (.leaf 1049))))) (.branch 184 (.branch 180 (.branch 178 (.branch 177 (.leaf 1051)
  (.leaf 1061)) (.branch 179 (.leaf 1063) (.leaf 1069))) (.branch 182 (.branch 181 (.leaf 1087)
  (.leaf 1091)) (.branch 183 (.leaf 1093) (.leaf 1097)))) (.branch 188 (.branch 186 (.branch 185
  (.leaf 1103) (.leaf 1109)) (.branch 187 (.leaf 1117) (.leaf 1123))) (.branch 190 (.branch 189
  (.leaf 1129) (.leaf 1151)) (.branch 191 (.leaf 1153) (.leaf 1163))))))) (.branch 224 (.branch 208
  (.branch 200 (.branch 196 (.branch 194 (.branch 193 (.leaf 1171) (.leaf 1181)) (.branch 195 (.leaf
  1187) (.leaf 1193))) (.branch 198 (.branch 197 (.leaf 1201) (.leaf 1213)) (.branch 199 (.leaf 1217)
  (.leaf 1223)))) (.branch 204 (.branch 202 (.branch 201 (.leaf 1229) (.leaf 1231)) (.branch 203
  (.leaf 1237) (.leaf 1249))) (.branch 206 (.branch 205 (.leaf 1259) (.leaf 1277)) (.branch 207
  (.leaf 1279) (.leaf 1283))))) (.branch 216 (.branch 212 (.branch 210 (.branch 209 (.leaf 1289)
  (.leaf 1291)) (.branch 211 (.leaf 1297) (.leaf 1301))) (.branch 214 (.branch 213 (.leaf 1303)
  (.leaf 1307)) (.branch 215 (.leaf 1319) (.leaf 1321)))) (.branch 220 (.branch 218 (.branch 217
  (.leaf 1327) (.leaf 1361)) (.branch 219 (.leaf 1367) (.leaf 1373))) (.branch 222 (.branch 221
  (.leaf 1381) (.leaf 1399)) (.branch 223 (.leaf 1409) (.leaf 1423)))))) (.branch 240 (.branch 232
  (.branch 228 (.branch 226 (.branch 225 (.leaf 1427) (.leaf 1429)) (.branch 227 (.leaf 1433) (.leaf
  1439))) (.branch 230 (.branch 229 (.leaf 1447) (.leaf 1451)) (.branch 231 (.leaf 1453) (.leaf
  1459)))) (.branch 236 (.branch 234 (.branch 233 (.leaf 1471) (.leaf 1481)) (.branch 235 (.leaf
  1483) (.leaf 1487))) (.branch 238 (.branch 237 (.leaf 1489) (.leaf 1493)) (.branch 239 (.leaf 1499)
  (.leaf 1511))))) (.branch 248 (.branch 244 (.branch 242 (.branch 241 (.leaf 1523) (.leaf 1531))
  (.branch 243 (.leaf 1543) (.leaf 1549))) (.branch 246 (.branch 245 (.leaf 1553) (.leaf 1559))
  (.branch 247 (.leaf 1567) (.leaf 1571)))) (.branch 252 (.branch 250 (.branch 249 (.leaf 1579)
  (.leaf 1583)) (.branch 251 (.leaf 1597) (.leaf 1601))) (.branch 254 (.branch 253 (.leaf 1607)
  (.leaf 1609)) (.branch 255 (.leaf 1613) (.leaf 1619))))))))) (.branch 384 (.branch 320 (.branch 288
  (.branch 272 (.branch 264 (.branch 260 (.branch 258 (.branch 257 (.leaf 1621) (.leaf 1627))
  (.branch 259 (.leaf 1637) (.leaf 1657))) (.branch 262 (.branch 261 (.leaf 1663) (.leaf 1667))
  (.branch 263 (.leaf 1669) (.leaf 1693)))) (.branch 268 (.branch 266 (.branch 265 (.leaf 1697)
  (.leaf 1699)) (.branch 267 (.leaf 1709) (.leaf 1721))) (.branch 270 (.branch 269 (.leaf 1723)
  (.leaf 1733)) (.branch 271 (.leaf 1741) (.leaf 1747))))) (.branch 280 (.branch 276 (.branch 274
  (.branch 273 (.leaf 1753) (.leaf 1759)) (.branch 275 (.leaf 1777) (.leaf 1783))) (.branch 278
  (.branch 277 (.leaf 1787) (.leaf 1789)) (.branch 279 (.leaf 1801) (.leaf 1811)))) (.branch 284
  (.branch 282 (.branch 281 (.leaf 1823) (.leaf 1831)) (.branch 283 (.leaf 1847) (.leaf 1861)))
  (.branch 286 (.branch 285 (.leaf 1867) (.leaf 1871)) (.branch 287 (.leaf 1873) (.leaf 1877))))))
  (.branch 304 (.branch 296 (.branch 292 (.branch 290 (.branch 289 (.leaf 1879) (.leaf 1889))
  (.branch 291 (.leaf 1901) (.leaf 1907))) (.branch 294 (.branch 293 (.leaf 1913) (.leaf 1931))
  (.branch 295 (.leaf 1933) (.leaf 1949)))) (.branch 300 (.branch 298 (.branch 297 (.leaf 1951)
  (.leaf 1973)) (.branch 299 (.leaf 1979) (.leaf 1987))) (.branch 302 (.branch 301 (.leaf 1993)
  (.leaf 1997)) (.branch 303 (.leaf 1999) (.leaf 2003))))) (.branch 312 (.branch 308 (.branch 306
  (.branch 305 (.leaf 2011) (.leaf 2017)) (.branch 307 (.leaf 2027) (.leaf 2029))) (.branch 310
  (.branch 309 (.leaf 2039) (.leaf 2053)) (.branch 311 (.leaf 2063) (.leaf 2069)))) (.branch 316
  (.branch 314 (.branch 313 (.leaf 2081) (.leaf 2083)) (.branch 315 (.leaf 2087) (.leaf 2089)))
  (.branch 318 (.branch 317 (.leaf 2099) (.leaf 2111)) (.branch 319 (.leaf 2113) (.leaf 2129)))))))
  (.branch 352 (.branch 336 (.branch 328 (.branch 324 (.branch 322 (.branch 321 (.leaf 2131) (.leaf
  2137)) (.branch 323 (.leaf 2141) (.leaf 2143))) (.branch 326 (.branch 325 (.leaf 2153) (.leaf
  2161)) (.branch 327 (.leaf 2179) (.leaf 2203)))) (.branch 332 (.branch 330 (.branch 329 (.leaf
  2207) (.leaf 2213)) (.branch 331 (.leaf 2221) (.leaf 2237))) (.branch 334 (.branch 333 (.leaf 2239)
  (.leaf 2243)) (.branch 335 (.leaf 2251) (.leaf 2267))))) (.branch 344 (.branch 340 (.branch 338
  (.branch 337 (.leaf 2269) (.leaf 2273)) (.branch 339 (.leaf 2281) (.leaf 2287))) (.branch 342
  (.branch 341 (.leaf 2293) (.leaf 2297)) (.branch 343 (.leaf 2309) (.leaf 2311)))) (.branch 348
  (.branch 346 (.branch 345 (.leaf 2333) (.leaf 2339)) (.branch 347 (.leaf 2341) (.leaf 2347)))
  (.branch 350 (.branch 349 (.leaf 2351) (.leaf 2357)) (.branch 351 (.leaf 2371) (.leaf 2377))))))
  (.branch 368 (.branch 360 (.branch 356 (.branch 354 (.branch 353 (.leaf 2381) (.leaf 2383))
  (.branch 355 (.leaf 2389) (.leaf 2393))) (.branch 358 (.branch 357 (.leaf 2399) (.leaf 2411))
  (.branch 359 (.leaf 2417) (.leaf 2423)))) (.branch 364 (.branch 362 (.branch 361 (.leaf 2437)
  (.leaf 2441)) (.branch 363 (.leaf 2447) (.leaf 2459))) (.branch 366 (.branch 365 (.leaf 2467)
  (.leaf 2473)) (.branch 367 (.leaf 2477) (.leaf 2503))))) (.branch 376 (.branch 372 (.branch 370
  (.branch 369 (.leaf 2521) (.leaf 2531)) (.branch 371 (.leaf 2539) (.leaf 2543))) (.branch 374
  (.branch 373 (.leaf 2549) (.leaf 2551)) (.branch 375 (.leaf 2557) (.leaf 2579)))) (.branch 380
  (.branch 378 (.branch 377 (.leaf 2591) (.leaf 2593)) (.branch 379 (.leaf 2609) (.leaf 2617)))
  (.branch 382 (.branch 381 (.leaf 2621) (.leaf 2633)) (.branch 383 (.leaf 2647) (.leaf 2657))))))))
  (.branch 448 (.branch 416 (.branch 400 (.branch 392 (.branch 388 (.branch 386 (.branch 385 (.leaf
  2659) (.leaf 2663)) (.branch 387 (.leaf 2671) (.leaf 2677))) (.branch 390 (.branch 389 (.leaf 2683)
  (.leaf 2687)) (.branch 391 (.leaf 2689) (.leaf 2693)))) (.branch 396 (.branch 394 (.branch 393
  (.leaf 2699) (.leaf 2707)) (.branch 395 (.leaf 2711) (.leaf 2713))) (.branch 398 (.branch 397
  (.leaf 2719) (.leaf 2729)) (.branch 399 (.leaf 2731) (.leaf 2741))))) (.branch 408 (.branch 404
  (.branch 402 (.branch 401 (.leaf 2749) (.leaf 2753)) (.branch 403 (.leaf 2767) (.leaf 2777)))
  (.branch 406 (.branch 405 (.leaf 2789) (.leaf 2791)) (.branch 407 (.leaf 2797) (.leaf 2801))))
  (.branch 412 (.branch 410 (.branch 409 (.leaf 2803) (.leaf 2819)) (.branch 411 (.leaf 2833) (.leaf
  2837))) (.branch 414 (.branch 413 (.leaf 2843) (.leaf 2851)) (.branch 415 (.leaf 2857) (.leaf
  2861)))))) (.branch 432 (.branch 424 (.branch 420 (.branch 418 (.branch 417 (.leaf 2879) (.leaf
  2887)) (.branch 419 (.leaf 2897) (.leaf 2903))) (.branch 422 (.branch 421 (.leaf 2909) (.leaf
  2917)) (.branch 423 (.leaf 2927) (.leaf 2939)))) (.branch 428 (.branch 426 (.branch 425 (.leaf
  2953) (.leaf 2957)) (.branch 427 (.leaf 2963) (.leaf 2969))) (.branch 430 (.branch 429 (.leaf 2971)
  (.leaf 2999)) (.branch 431 (.leaf 3001) (.leaf 3011))))) (.branch 440 (.branch 436 (.branch 434
  (.branch 433 (.leaf 3019) (.leaf 3023)) (.branch 435 (.leaf 3037) (.leaf 3041))) (.branch 438
  (.branch 437 (.leaf 3049) (.leaf 3061)) (.branch 439 (.leaf 3067) (.leaf 3079)))) (.branch 444
  (.branch 442 (.branch 441 (.leaf 3083) (.leaf 3089)) (.branch 443 (.leaf 3109) (.leaf 3119)))
  (.branch 446 (.branch 445 (.leaf 3121) (.leaf 3137)) (.branch 447 (.leaf 3163) (.leaf 3167)))))))
  (.branch 480 (.branch 464 (.branch 456 (.branch 452 (.branch 450 (.branch 449 (.leaf 3169) (.leaf
  3181)) (.branch 451 (.leaf 3187) (.leaf 3191))) (.branch 454 (.branch 453 (.leaf 3203) (.leaf
  3209)) (.branch 455 (.leaf 3217) (.leaf 3221)))) (.branch 460 (.branch 458 (.branch 457 (.leaf
  3229) (.leaf 3251)) (.branch 459 (.leaf 3253) (.leaf 3257))) (.branch 462 (.branch 461 (.leaf 3259)
  (.leaf 3271)) (.branch 463 (.leaf 3299) (.leaf 3301))))) (.branch 472 (.branch 468 (.branch 466
  (.branch 465 (.leaf 3307) (.leaf 3313)) (.branch 467 (.leaf 3319) (.leaf 3323))) (.branch 470
  (.branch 469 (.leaf 3329) (.leaf 3331)) (.branch 471 (.leaf 3343) (.leaf 3347)))) (.branch 476
  (.branch 474 (.branch 473 (.leaf 3359) (.leaf 3361)) (.branch 475 (.leaf 3371) (.leaf 3373)))
  (.branch 478 (.branch 477 (.leaf 3389) (.leaf 3391)) (.branch 479 (.leaf 3407) (.leaf 3413))))))
  (.branch 496 (.branch 488 (.branch 484 (.branch 482 (.branch 481 (.leaf 3433) (.leaf 3449))
  (.branch 483 (.leaf 3457) (.leaf 3461))) (.branch 486 (.branch 485 (.leaf 3463) (.leaf 3467))
  (.branch 487 (.leaf 3469) (.leaf 3491)))) (.branch 492 (.branch 490 (.branch 489 (.leaf 3499)
  (.leaf 3511)) (.branch 491 (.leaf 3517) (.leaf 3527))) (.branch 494 (.branch 493 (.leaf 3529)
  (.leaf 3533)) (.branch 495 (.leaf 3539) (.leaf 3541))))) (.branch 504 (.branch 500 (.branch 498
  (.branch 497 (.leaf 3547) (.leaf 3557)) (.branch 499 (.leaf 3559) (.leaf 3571))) (.branch 502
  (.branch 501 (.leaf 3581) (.leaf 3583)) (.branch 503 (.leaf 3593) (.leaf 3607)))) (.branch 508
  (.branch 506 (.branch 505 (.leaf 3613) (.leaf 3617)) (.branch 507 (.leaf 3623) (.leaf 3631)))
  (.branch 510 (.branch 509 (.leaf 3637) (.leaf 3643)) (.branch 511 (.leaf 3659) (.leaf
  3671)))))))))) (.branch 768 (.branch 640 (.branch 576 (.branch 544 (.branch 528 (.branch 520
  (.branch 516 (.branch 514 (.branch 513 (.leaf 3673) (.leaf 3677)) (.branch 515 (.leaf 3691) (.leaf
  3697))) (.branch 518 (.branch 517 (.leaf 3701) (.leaf 3709)) (.branch 519 (.leaf 3719) (.leaf
  3727)))) (.branch 524 (.branch 522 (.branch 521 (.leaf 3733) (.leaf 3739)) (.branch 523 (.leaf
  3761) (.leaf 3767))) (.branch 526 (.branch 525 (.leaf 3769) (.leaf 3779)) (.branch 527 (.leaf 3793)
  (.leaf 3797))))) (.branch 536 (.branch 532 (.branch 530 (.branch 529 (.leaf 3803) (.leaf 3821))
  (.branch 531 (.leaf 3823) (.leaf 3833))) (.branch 534 (.branch 533 (.leaf 3847) (.leaf 3851))
  (.branch 535 (.leaf 3853) (.leaf 3863)))) (.branch 540 (.branch 538 (.branch 537 (.leaf 3877)
  (.leaf 3881)) (.branch 539 (.leaf 3889) (.leaf 3907))) (.branch 542 (.branch 541 (.leaf 3911)
  (.leaf 3917)) (.branch 543 (.leaf 3919) (.leaf 3923)))))) (.branch 560 (.branch 552 (.branch 548
  (.branch 546 (.branch 545 (.leaf 3929) (.leaf 3931)) (.branch 547 (.leaf 3943) (.leaf 3947)))
  (.branch 550 (.branch 549 (.leaf 3967) (.leaf 3989)) (.branch 551 (.leaf 4001) (.leaf 4003))))
  (.branch 556 (.branch 554 (.branch 553 (.leaf 4007) (.leaf 4013)) (.branch 555 (.leaf 4019) (.leaf
  4021))) (.branch 558 (.branch 557 (.leaf 4027) (.leaf 4049)) (.branch 559 (.leaf 4051) (.leaf
  4057))))) (.branch 568 (.branch 564 (.branch 562 (.branch 561 (.leaf 4073) (.leaf 4079)) (.branch
  563 (.leaf 4091) (.leaf 4093))) (.branch 566 (.branch 565 (.leaf 4099) (.leaf 4111)) (.branch 567
  (.leaf 4127) (.leaf 4129)))) (.branch 572 (.branch 570 (.branch 569 (.leaf 4133) (.leaf 4139))
  (.branch 571 (.leaf 4153) (.leaf 4157))) (.branch 574 (.branch 573 (.leaf 4159) (.leaf 4177))
  (.branch 575 (.leaf 4201) (.leaf 4211))))))) (.branch 608 (.branch 592 (.branch 584 (.branch 580
  (.branch 578 (.branch 577 (.leaf 4217) (.leaf 4219)) (.branch 579 (.leaf 4229) (.leaf 4231)))
  (.branch 582 (.branch 581 (.leaf 4241) (.leaf 4243)) (.branch 583 (.leaf 4253) (.leaf 4259))))
  (.branch 588 (.branch 586 (.branch 585 (.leaf 4261) (.leaf 4271)) (.branch 587 (.leaf 4273) (.leaf
  4283))) (.branch 590 (.branch 589 (.leaf 4289) (.leaf 4297)) (.branch 591 (.leaf 4327) (.leaf
  4337))))) (.branch 600 (.branch 596 (.branch 594 (.branch 593 (.leaf 4339) (.leaf 4349)) (.branch
  595 (.leaf 4357) (.leaf 4363))) (.branch 598 (.branch 597 (.leaf 4373) (.leaf 4391)) (.branch 599
  (.leaf 4397) (.leaf 4409)))) (.branch 604 (.branch 602 (.branch 601 (.leaf 4421) (.leaf 4423))
  (.branch 603 (.leaf 4441) (.leaf 4447))) (.branch 606 (.branch 605 (.leaf 4451) (.leaf 4457))
  (.branch 607 (.leaf 4463) (.leaf 4481)))))) (.branch 624 (.branch 616 (.branch 612 (.branch 610
  (.branch 609 (.leaf 4483) (.leaf 4493)) (.branch 611 (.leaf 4507) (.leaf 4513))) (.branch 614
  (.branch 613 (.leaf 4517) (.leaf 4519)) (.branch 615 (.leaf 4523) (.leaf 4547)))) (.branch 620
  (.branch 618 (.branch 617 (.leaf 4549) (.leaf 4561)) (.branch 619 (.leaf 4567) (.leaf 4583)))
  (.branch 622 (.branch 621 (.leaf 4591) (.leaf 4597)) (.branch 623 (.leaf 4603) (.leaf 4621)))))
  (.branch 632 (.branch 628 (.branch 626 (.branch 625 (.leaf 4637) (.leaf 4639)) (.branch 627 (.leaf
  4643) (.leaf 4649))) (.branch 630 (.branch 629 (.leaf 4651) (.leaf 4657)) (.branch 631 (.leaf 4663)
  (.leaf 4673)))) (.branch 636 (.branch 634 (.branch 633 (.leaf 4679) (.leaf 4691)) (.branch 635
  (.leaf 4703) (.leaf 4721))) (.branch 638 (.branch 637 (.leaf 4723) (.leaf 4729)) (.branch 639
  (.leaf 4733) (.leaf 4751)))))))) (.branch 704 (.branch 672 (.branch 656 (.branch 648 (.branch 644
  (.branch 642 (.branch 641 (.leaf 4759) (.leaf 4783)) (.branch 643 (.leaf 4787) (.leaf 4789)))
  (.branch 646 (.branch 645 (.leaf 4793) (.leaf 4799)) (.branch 647 (.leaf 4801) (.leaf 4813))))
  (.branch 652 (.branch 650 (.branch 649 (.leaf 4817) (.leaf 4831)) (.branch 651 (.leaf 4861) (.leaf
  4871))) (.branch 654 (.branch 653 (.leaf 4877) (.leaf 4889)) (.branch 655 (.leaf 4903) (.leaf
  4909))))) (.branch 664 (.branch 660 (.branch 658 (.branch 657 (.leaf 4919) (.leaf 4931)) (.branch
  659 (.leaf 4933) (.leaf 4937))) (.branch 662 (.branch 661 (.leaf 4943) (.leaf 4951)) (.branch 663
  (.leaf 4957) (.leaf 4967)))) (.branch 668 (.branch 666 (.branch 665 (.leaf 4969) (.leaf 4973))
  (.branch 667 (.leaf 4987) (.leaf 4993))) (.branch 670 (.branch 669 (.leaf 4999) (.leaf 5003))
  (.branch 671 (.leaf 5009) (.leaf 5011)))))) (.branch 688 (.branch 680 (.branch 676 (.branch 674
  (.branch 673 (.leaf 5021) (.leaf 5023)) (.branch 675 (.leaf 5039) (.leaf 5051))) (.branch 678
  (.branch 677 (.leaf 5059) (.leaf 5077)) (.branch 679 (.leaf 5081) (.leaf 5087)))) (.branch 684
  (.branch 682 (.branch 681 (.leaf 5099) (.leaf 5101)) (.branch 683 (.leaf 5107) (.leaf 5113)))
  (.branch 686 (.branch 685 (.leaf 5119) (.leaf 5147)) (.branch 687 (.leaf 5153) (.leaf 5167)))))
  (.branch 696 (.branch 692 (.branch 690 (.branch 689 (.leaf 5171) (.leaf 5179)) (.branch 691 (.leaf
  5189) (.leaf 5197))) (.branch 694 (.branch 693 (.leaf 5209) (.leaf 5227)) (.branch 695 (.leaf 5231)
  (.leaf 5233)))) (.branch 700 (.branch 698 (.branch 697 (.leaf 5237) (.leaf 5261)) (.branch 699
  (.leaf 5273) (.leaf 5279))) (.branch 702 (.branch 701 (.leaf 5281) (.leaf 5297)) (.branch 703
  (.leaf 5303) (.leaf 5309))))))) (.branch 736 (.branch 720 (.branch 712 (.branch 708 (.branch 706
  (.branch 705 (.leaf 5323) (.leaf 5333)) (.branch 707 (.leaf 5347) (.leaf 5351))) (.branch 710
  (.branch 709 (.leaf 5381) (.leaf 5387)) (.branch 711 (.leaf 5393) (.leaf 5399)))) (.branch 716
  (.branch 714 (.branch 713 (.leaf 5407) (.leaf 5413)) (.branch 715 (.leaf 5417) (.leaf 5419)))
  (.branch 718 (.branch 717 (.leaf 5431) (.leaf 5437)) (.branch 719 (.leaf 5441) (.leaf 5443)))))
  (.branch 728 (.branch 724 (.branch 722 (.branch 721 (.leaf 5449) (.leaf 5471)) (.branch 723 (.leaf
  5477) (.leaf 5479))) (.branch 726 (.branch 725 (.leaf 5483) (.leaf 5501)) (.branch 727 (.leaf 5503)
  (.leaf 5507)))) (.branch 732 (.branch 730 (.branch 729 (.leaf 5519) (.leaf 5521)) (.branch 731
  (.leaf 5527) (.leaf 5531))) (.branch 734 (.branch 733 (.leaf 5557) (.leaf 5563)) (.branch 735
  (.leaf 5569) (.leaf 5573)))))) (.branch 752 (.branch 744 (.branch 740 (.branch 738 (.branch 737
  (.leaf 5581) (.leaf 5591)) (.branch 739 (.leaf 5623) (.leaf 5639))) (.branch 742 (.branch 741
  (.leaf 5641) (.leaf 5647)) (.branch 743 (.leaf 5651) (.leaf 5653)))) (.branch 748 (.branch 746
  (.branch 745 (.leaf 5657) (.leaf 5659)) (.branch 747 (.leaf 5669) (.leaf 5683))) (.branch 750
  (.branch 749 (.leaf 5689) (.leaf 5693)) (.branch 751 (.leaf 5701) (.leaf 5711))))) (.branch 760
  (.branch 756 (.branch 754 (.branch 753 (.leaf 5717) (.leaf 5737)) (.branch 755 (.leaf 5741) (.leaf
  5743))) (.branch 758 (.branch 757 (.leaf 5749) (.leaf 5779)) (.branch 759 (.leaf 5783) (.leaf
  5791)))) (.branch 764 (.branch 762 (.branch 761 (.leaf 5801) (.leaf 5807)) (.branch 763 (.leaf
  5813) (.leaf 5821))) (.branch 766 (.branch 765 (.leaf 5827) (.leaf 5839)) (.branch 767 (.leaf 5843)
  (.leaf 5849))))))))) (.branch 896 (.branch 832 (.branch 800 (.branch 784 (.branch 776 (.branch 772
  (.branch 770 (.branch 769 (.leaf 5851) (.leaf 5857)) (.branch 771 (.leaf 5861) (.leaf 5867)))
  (.branch 774 (.branch 773 (.leaf 5869) (.leaf 5879)) (.branch 775 (.leaf 5881) (.leaf 5897))))
  (.branch 780 (.branch 778 (.branch 777 (.leaf 5903) (.leaf 5923)) (.branch 779 (.leaf 5927) (.leaf
  5939))) (.branch 782 (.branch 781 (.leaf 5953) (.leaf 5981)) (.branch 783 (.leaf 5987) (.leaf
  6007))))) (.branch 792 (.branch 788 (.branch 786 (.branch 785 (.leaf 6011) (.leaf 6029)) (.branch
  787 (.leaf 6037) (.leaf 6043))) (.branch 790 (.branch 789 (.leaf 6047) (.leaf 6053)) (.branch 791
  (.leaf 6067) (.leaf 6073)))) (.branch 796 (.branch 794 (.branch 793 (.leaf 6079) (.leaf 6089))
  (.branch 795 (.leaf 6091) (.leaf 6101))) (.branch 798 (.branch 797 (.leaf 6113) (.leaf 6121))
  (.branch 799 (.leaf 6131) (.leaf 6133)))))) (.branch 816 (.branch 808 (.branch 804 (.branch 802
  (.branch 801 (.leaf 6143) (.leaf 6151)) (.branch 803 (.leaf 6163) (.leaf 6173))) (.branch 806
  (.branch 805 (.leaf 6197) (.leaf 6199)) (.branch 807 (.leaf 6203) (.leaf 6211)))) (.branch 812
  (.branch 810 (.branch 809 (.leaf 6217) (.leaf 6221)) (.branch 811 (.leaf 6229) (.leaf 6247)))
  (.branch 814 (.branch 813 (.leaf 6257) (.leaf 6263)) (.branch 815 (.leaf 6269) (.leaf 6271)))))
  (.branch 824 (.branch 820 (.branch 818 (.branch 817 (.leaf 6277) (.leaf 6287)) (.branch 819 (.leaf
  6299) (.leaf 6301))) (.branch 822 (.branch 821 (.leaf 6311) (.leaf 6317)) (.branch 823 (.leaf 6323)
  (.leaf 6329)))) (.branch 828 (.branch 826 (.branch 825 (.leaf 6337) (.leaf 6343)) (.branch 827
  (.leaf 6353) (.leaf 6359))) (.branch 830 (.branch 829 (.leaf 6361) (.leaf 6367)) (.branch 831
  (.leaf 6373) (.leaf 6379))))))) (.branch 864 (.branch 848 (.branch 840 (.branch 836 (.branch 834
  (.branch 833 (.leaf 6389) (.leaf 6397)) (.branch 835 (.leaf 6421) (.leaf 6427))) (.branch 838
  (.branch 837 (.leaf 6449) (.leaf 6451)) (.branch 839 (.leaf 6469) (.leaf 6473)))) (.branch 844
  (.branch 842 (.branch 841 (.leaf 6481) (.leaf 6491)) (.branch 843 (.leaf 6521) (.leaf 6529)))
  (.branch 846 (.branch 845 (.leaf 6547) (.leaf 6551)) (.branch 847 (.leaf 6553) (.leaf 6563)))))
  (.branch 856 (.branch 852 (.branch 850 (.branch 849 (.leaf 6569) (.leaf 6571)) (.branch 851 (.leaf
  6577) (.leaf 6581))) (.branch 854 (.branch 853 (.leaf 6599) (.leaf 6607)) (.branch 855 (.leaf 6619)
  (.leaf 6637)))) (.branch 860 (.branch 858 (.branch 857 (.leaf 6653) (.leaf 6659)) (.branch 859
  (.leaf 6661) (.leaf 6673))) (.branch 862 (.branch 861 (.leaf 6679) (.leaf 6689)) (.branch 863
  (.leaf 6691) (.leaf 6701)))))) (.branch 880 (.branch 872 (.branch 868 (.branch 866 (.branch 865
  (.leaf 6703) (.leaf 6709)) (.branch 867 (.leaf 6719) (.leaf 6733))) (.branch 870 (.branch 869
  (.leaf 6737) (.leaf 6761)) (.branch 871 (.leaf 6763) (.leaf 6779)))) (.branch 876 (.branch 874
  (.branch 873 (.leaf 6781) (.leaf 6791)) (.branch 875 (.leaf 6793) (.leaf 6803))) (.branch 878
  (.branch 877 (.leaf 6823) (.leaf 6827)) (.branch 879 (.leaf 6829) (.leaf 6833))))) (.branch 888
  (.branch 884 (.branch 882 (.branch 881 (.leaf 6841) (.leaf 6857)) (.branch 883 (.leaf 6863) (.leaf
  6869))) (.branch 886 (.branch 885 (.leaf 6871) (.leaf 6883)) (.branch 887 (.leaf 6899) (.leaf
  6907)))) (.branch 892 (.branch 890 (.branch 889 (.leaf 6911) (.leaf 6917)) (.branch 891 (.leaf
  6947) (.leaf 6949))) (.branch 894 (.branch 893 (.leaf 6959) (.leaf 6961)) (.branch 895 (.leaf 6967)
  (.leaf 6971)))))))) (.branch 960 (.branch 928 (.branch 912 (.branch 904 (.branch 900 (.branch 898
  (.branch 897 (.leaf 6977) (.leaf 6983)) (.branch 899 (.leaf 6991) (.leaf 6997))) (.branch 902
  (.branch 901 (.leaf 7001) (.leaf 7013)) (.branch 903 (.leaf 7019) (.leaf 7027)))) (.branch 908
  (.branch 906 (.branch 905 (.leaf 7039) (.leaf 7043)) (.branch 907 (.leaf 7057) (.leaf 7069)))
  (.branch 910 (.branch 909 (.leaf 7079) (.leaf 7103)) (.branch 911 (.leaf 7109) (.leaf 7121)))))
  (.branch 920 (.branch 916 (.branch 914 (.branch 913 (.leaf 7127) (.leaf 7129)) (.branch 915 (.leaf
  7151) (.leaf 7159))) (.branch 918 (.branch 917 (.leaf 7177) (.leaf 7187)) (.branch 919 (.leaf 7193)
  (.leaf 7207)))) (.branch 924 (.branch 922 (.branch 921 (.leaf 7211) (.leaf 7213)) (.branch 923
  (.leaf 7219) (.leaf 7229))) (.branch 926 (.branch 925 (.leaf 7237) (.leaf 7243)) (.branch 927
  (.leaf 7247) (.leaf 7253)))))) (.branch 944 (.branch 936 (.branch 932 (.branch 930 (.branch 929
  (.leaf 7283) (.leaf 7297)) (.branch 931 (.leaf 7307) (.leaf 7309))) (.branch 934 (.branch 933
  (.leaf 7321) (.leaf 7331)) (.branch 935 (.leaf 7333) (.leaf 7349)))) (.branch 940 (.branch 938
  (.branch 937 (.leaf 7351) (.leaf 7369)) (.branch 939 (.leaf 7393) (.leaf 7411))) (.branch 942
  (.branch 941 (.leaf 7417) (.leaf 7433)) (.branch 943 (.leaf 7451) (.leaf 7457))))) (.branch 952
  (.branch 948 (.branch 946 (.branch 945 (.leaf 7459) (.leaf 7477)) (.branch 947 (.leaf 7481) (.leaf
  7487))) (.branch 950 (.branch 949 (.leaf 7489) (.leaf 7499)) (.branch 951 (.leaf 7507) (.leaf
  7517)))) (.branch 956 (.branch 954 (.branch 953 (.leaf 7523) (.leaf 7529)) (.branch 955 (.leaf
  7537) (.leaf 7541))) (.branch 958 (.branch 957 (.leaf 7547) (.leaf 7549)) (.branch 959 (.leaf 7559)
  (.leaf 7561))))))) (.branch 992 (.branch 976 (.branch 968 (.branch 964 (.branch 962 (.branch 961
  (.leaf 7573) (.leaf 7577)) (.branch 963 (.leaf 7583) (.leaf 7589))) (.branch 966 (.branch 965
  (.leaf 7591) (.leaf 7603)) (.branch 967 (.leaf 7607) (.leaf 7621)))) (.branch 972 (.branch 970
  (.branch 969 (.leaf 7639) (.leaf 7643)) (.branch 971 (.leaf 7649) (.leaf 7669))) (.branch 974
  (.branch 973 (.leaf 7673) (.leaf 7681)) (.branch 975 (.leaf 7687) (.leaf 7691))))) (.branch 984
  (.branch 980 (.branch 978 (.branch 977 (.leaf 7699) (.leaf 7703)) (.branch 979 (.leaf 7717) (.leaf
  7723))) (.branch 982 (.branch 981 (.leaf 7727) (.leaf 7741)) (.branch 983 (.leaf 7753) (.leaf
  7757)))) (.branch 988 (.branch 986 (.branch 985 (.leaf 7759) (.leaf 7789)) (.branch 987 (.leaf
  7793) (.leaf 7817))) (.branch 990 (.branch 989 (.leaf 7823) (.leaf 7829)) (.branch 991 (.leaf 7841)
  (.leaf 7853)))))) (.branch 1008 (.branch 1000 (.branch 996 (.branch 994 (.branch 993 (.leaf 7867)
  (.leaf 7873)) (.branch 995 (.leaf 7877) (.leaf 7879))) (.branch 998 (.branch 997 (.leaf 7883)
  (.leaf 7901)) (.branch 999 (.leaf 7907) (.leaf 7919)))) (.branch 1004 (.branch 1002 (.branch 1001
  (.leaf 7927) (.leaf 7933)) (.branch 1003 (.leaf 7937) (.leaf 7949))) (.branch 1006 (.branch 1005
  (.leaf 7951) (.leaf 7963)) (.branch 1007 (.leaf 7993) (.leaf 8009))))) (.branch 1016 (.branch 1012
  (.branch 1010 (.branch 1009 (.leaf 8011) (.leaf 8017)) (.branch 1011 (.leaf 8039) (.leaf 8053)))
  (.branch 1014 (.branch 1013 (.leaf 8059) (.leaf 8069)) (.branch 1015 (.leaf 8081) (.leaf 8087))))
  (.branch 1020 (.branch 1018 (.branch 1017 (.leaf 8089) (.leaf 8093)) (.branch 1019 (.leaf 8101)
  (.leaf 8111))) (.branch 1022 (.branch 1021 (.leaf 8117) (.leaf 8123)) (.branch 1023 (.leaf 8147)
  (.leaf 8161))))))))))) (.branch 1536 (.branch 1280 (.branch 1152 (.branch 1088 (.branch 1056
  (.branch 1040 (.branch 1032 (.branch 1028 (.branch 1026 (.branch 1025 (.leaf 8167) (.leaf 8171))
  (.branch 1027 (.leaf 8179) (.leaf 8191))) (.branch 1030 (.branch 1029 (.leaf 8209) (.leaf 8219))
  (.branch 1031 (.leaf 8221) (.leaf 8231)))) (.branch 1036 (.branch 1034 (.branch 1033 (.leaf 8233)
  (.leaf 8237)) (.branch 1035 (.leaf 8243) (.leaf 8263))) (.branch 1038 (.branch 1037 (.leaf 8269)
  (.leaf 8273)) (.branch 1039 (.leaf 8287) (.leaf 8291))))) (.branch 1048 (.branch 1044 (.branch 1042
  (.branch 1041 (.leaf 8293) (.leaf 8297)) (.branch 1043 (.leaf 8311) (.leaf 8317))) (.branch 1046
  (.branch 1045 (.leaf 8329) (.leaf 8353)) (.branch 1047 (.leaf 8363) (.leaf 8369)))) (.branch 1052
  (.branch 1050 (.branch 1049 (.leaf 8377) (.leaf 8387)) (.branch 1051 (.leaf 8389) (.leaf 8419)))
  (.branch 1054 (.branch 1053 (.leaf 8423) (.leaf 8429)) (.branch 1055 (.leaf 8431) (.leaf 8443))))))
  (.branch 1072 (.branch 1064 (.branch 1060 (.branch 1058 (.branch 1057 (.leaf 8447) (.leaf 8461))
  (.branch 1059 (.leaf 8467) (.leaf 8501))) (.branch 1062 (.branch 1061 (.leaf 8513) (.leaf 8521))
  (.branch 1063 (.leaf 8527) (.leaf 8537)))) (.branch 1068 (.branch 1066 (.branch 1065 (.leaf 8539)
  (.leaf 8543)) (.branch 1067 (.leaf 8563) (.leaf 8573))) (.branch 1070 (.branch 1069 (.leaf 8581)
  (.leaf 8597)) (.branch 1071 (.leaf 8599) (.leaf 8609))))) (.branch 1080 (.branch 1076 (.branch 1074
  (.branch 1073 (.leaf 8623) (.leaf 8627)) (.branch 1075 (.leaf 8629) (.leaf 8641))) (.branch 1078
  (.branch 1077 (.leaf 8647) (.leaf 8663)) (.branch 1079 (.leaf 8669) (.leaf 8677)))) (.branch 1084
  (.branch 1082 (.branch 1081 (.leaf 8681) (.leaf 8689)) (.branch 1083 (.leaf 8693) (.leaf 8699)))
  (.branch 1086 (.branch 1085 (.leaf 8707) (.leaf 8713)) (.branch 1087 (.leaf 8719) (.leaf
  8731))))))) (.branch 1120 (.branch 1104 (.branch 1096 (.branch 1092 (.branch 1090 (.branch 1089
  (.leaf 8737) (.leaf 8741)) (.branch 1091 (.leaf 8747) (.leaf 8753))) (.branch 1094 (.branch 1093
  (.leaf 8761) (.leaf 8779)) (.branch 1095 (.leaf 8783) (.leaf 8803)))) (.branch 1100 (.branch 1098
  (.branch 1097 (.leaf 8807) (.leaf 8819)) (.branch 1099 (.leaf 8821) (.leaf 8831))) (.branch 1102
  (.branch 1101 (.leaf 8837) (.leaf 8839)) (.branch 1103 (.leaf 8849) (.leaf 8861))))) (.branch 1112
  (.branch 1108 (.branch 1106 (.branch 1105 (.leaf 8863) (.leaf 8867)) (.branch 1107 (.leaf 8887)
  (.leaf 8893))) (.branch 1110 (.branch 1109 (.leaf 8923) (.leaf 8929)) (.branch 1111 (.leaf 8933)
  (.leaf 8941)))) (.branch 1116 (.branch 1114 (.branch 1113 (.leaf 8951) (.leaf 8963)) (.branch 1115
  (.leaf 8969) (.leaf 8971))) (.branch 1118 (.branch 1117 (.leaf 8999) (.leaf 9001)) (.branch 1119
  (.leaf 9007) (.leaf 9011)))))) (.branch 1136 (.branch 1128 (.branch 1124 (.branch 1122 (.branch
  1121 (.leaf 9013) (.leaf 9029)) (.branch 1123 (.leaf 9041) (.leaf 9043))) (.branch 1126 (.branch
  1125 (.leaf 9049) (.leaf 9059)) (.branch 1127 (.leaf 9067) (.leaf 9091)))) (.branch 1132 (.branch
  1130 (.branch 1129 (.leaf 9103) (.leaf 9109)) (.branch 1131 (.leaf 9127) (.leaf 9133))) (.branch
  1134 (.branch 1133 (.leaf 9137) (.leaf 9151)) (.branch 1135 (.leaf 9157) (.leaf 9161))))) (.branch
  1144 (.branch 1140 (.branch 1138 (.branch 1137 (.leaf 9173) (.leaf 9181)) (.branch 1139 (.leaf
  9187) (.leaf 9199))) (.branch 1142 (.branch 1141 (.leaf 9203) (.leaf 9209)) (.branch 1143 (.leaf
  9221) (.leaf 9227)))) (.branch 1148 (.branch 1146 (.branch 1145 (.leaf 9239) (.leaf 9241)) (.branch
  1147 (.leaf 9257) (.leaf 9277))) (.branch 1150 (.branch 1149 (.leaf 9281) (.leaf 9283)) (.branch
  1151 (.leaf 9293) (.leaf 9311)))))))) (.branch 1216 (.branch 1184 (.branch 1168 (.branch 1160
  (.branch 1156 (.branch 1154 (.branch 1153 (.leaf 9319) (.leaf 9323)) (.branch 1155 (.leaf 9337)
  (.leaf 9341))) (.branch 1158 (.branch 1157 (.leaf 9343) (.leaf 9349)) (.branch 1159 (.leaf 9371)
  (.leaf 9377)))) (.branch 1164 (.branch 1162 (.branch 1161 (.leaf 9391) (.leaf 9397)) (.branch 1163
  (.leaf 9403) (.leaf 9413))) (.branch 1166 (.branch 1165 (.leaf 9419) (.leaf 9421)) (.branch 1167
  (.leaf 9431) (.leaf 9433))))) (.branch 1176 (.branch 1172 (.branch 1170 (.branch 1169 (.leaf 9437)
  (.leaf 9439)) (.branch 1171 (.leaf 9461) (.leaf 9463))) (.branch 1174 (.branch 1173 (.leaf 9467)
  (.leaf 9473)) (.branch 1175 (.leaf 9479) (.leaf 9491)))) (.branch 1180 (.branch 1178 (.branch 1177
  (.leaf 9497) (.leaf 9511)) (.branch 1179 (.leaf 9521) (.leaf 9533))) (.branch 1182 (.branch 1181
  (.leaf 9539) (.leaf 9547)) (.branch 1183 (.leaf 9551) (.leaf 9587)))))) (.branch 1200 (.branch 1192
  (.branch 1188 (.branch 1186 (.branch 1185 (.leaf 9601) (.leaf 9613)) (.branch 1187 (.leaf 9619)
  (.leaf 9623))) (.branch 1190 (.branch 1189 (.leaf 9629) (.leaf 9631)) (.branch 1191 (.leaf 9643)
  (.leaf 9649)))) (.branch 1196 (.branch 1194 (.branch 1193 (.leaf 9661) (.leaf 9677)) (.branch 1195
  (.leaf 9679) (.leaf 9689))) (.branch 1198 (.branch 1197 (.leaf 9697) (.leaf 9719)) (.branch 1199
  (.leaf 9721) (.leaf 9733))))) (.branch 1208 (.branch 1204 (.branch 1202 (.branch 1201 (.leaf 9739)
  (.leaf 9743)) (.branch 1203 (.leaf 9749) (.leaf 9767))) (.branch 1206 (.branch 1205 (.leaf 9769)
  (.leaf 9781)) (.branch 1207 (.leaf 9787) (.leaf 9791)))) (.branch 1212 (.branch 1210 (.branch 1209
  (.leaf 9803) (.leaf 9811)) (.branch 1211 (.leaf 9817) (.leaf 9829))) (.branch 1214 (.branch 1213
  (.leaf 9833) (.leaf 9839)) (.branch 1215 (.leaf 9851) (.leaf 9857))))))) (.branch 1248 (.branch
  1232 (.branch 1224 (.branch 1220 (.branch 1218 (.branch 1217 (.leaf 9859) (.leaf 9871)) (.branch
  1219 (.leaf 9883) (.leaf 9887))) (.branch 1222 (.branch 1221 (.leaf 9901) (.leaf 9907)) (.branch
  1223 (.leaf 9923) (.leaf 9929)))) (.branch 1228 (.branch 1226 (.branch 1225 (.leaf 9931) (.leaf
  9941)) (.branch 1227 (.leaf 9949) (.leaf 9967))) (.branch 1230 (.branch 1229 (.leaf 9973) (.leaf
  10007)) (.branch 1231 (.leaf 10009) (.leaf 10037))))) (.branch 1240 (.branch 1236 (.branch 1234
  (.branch 1233 (.leaf 10039) (.leaf 10061)) (.branch 1235 (.leaf 10067) (.leaf 10069))) (.branch
  1238 (.branch 1237 (.leaf 10079) (.leaf 10091)) (.branch 1239 (.leaf 10093) (.leaf 10099))))
  (.branch 1244 (.branch 1242 (.branch 1241 (.leaf 10103) (.leaf 10111)) (.branch 1243 (.leaf 10133)
  (.leaf 10139))) (.branch 1246 (.branch 1245 (.leaf 10141) (.leaf 10151)) (.branch 1247 (.leaf
  10159) (.leaf 10163)))))) (.branch 1264 (.branch 1256 (.branch 1252 (.branch 1250 (.branch 1249
  (.leaf 10169) (.leaf 10177)) (.branch 1251 (.leaf 10181) (.leaf 10193))) (.branch 1254 (.branch
  1253 (.leaf 10211) (.leaf 10223)) (.branch 1255 (.leaf 10243) (.leaf 10247)))) (.branch 1260
  (.branch 1258 (.branch 1257 (.leaf 10253) (.leaf 10259)) (.branch 1259 (.leaf 10267) (.leaf
  10271))) (.branch 1262 (.branch 1261 (.leaf 10273) (.leaf 10289)) (.branch 1263 (.leaf 10301)
  (.leaf 10303))))) (.branch 1272 (.branch 1268 (.branch 1266 (.branch 1265 (.leaf 10313) (.leaf
  10321)) (.branch 1267 (.leaf 10331) (.leaf 10333))) (.branch 1270 (.branch 1269 (.leaf 10337)
  (.leaf 10343)) (.branch 1271 (.leaf 10357) (.leaf 10369)))) (.branch 1276 (.branch 1274 (.branch
  1273 (.leaf 10391) (.leaf 10399)) (.branch 1275 (.leaf 10427) (.leaf 10429))) (.branch 1278
  (.branch 1277 (.leaf 10433) (.leaf 10453)) (.branch 1279 (.leaf 10457) (.leaf 10459)))))))))
  (.branch 1408 (.branch 1344 (.branch 1312 (.branch 1296 (.branch 1288 (.branch 1284 (.branch 1282
  (.branch 1281 (.leaf 10463) (.leaf 10477)) (.branch 1283 (.leaf 10487) (.leaf 10499))) (.branch
  1286 (.branch 1285 (.leaf 10501) (.leaf 10513)) (.branch 1287 (.leaf 10529) (.leaf 10531))))
  (.branch 1292 (.branch 1290 (.branch 1289 (.leaf 10559) (.leaf 10567)) (.branch 1291 (.leaf 10589)
  (.leaf 10597))) (.branch 1294 (.branch 1293 (.leaf 10601) (.leaf 10607)) (.branch 1295 (.leaf
  10613) (.leaf 10627))))) (.branch 1304 (.branch 1300 (.branch 1298 (.branch 1297 (.leaf 10631)
  (.leaf 10639)) (.branch 1299 (.leaf 10651) (.leaf 10657))) (.branch 1302 (.branch 1301 (.leaf
  10663) (.leaf 10667)) (.branch 1303 (.leaf 10687) (.leaf 10691)))) (.branch 1308 (.branch 1306
  (.branch 1305 (.leaf 10709) (.leaf 10711)) (.branch 1307 (.leaf 10723) (.leaf 10729))) (.branch
  1310 (.branch 1309 (.leaf 10733) (.leaf 10739)) (.branch 1311 (.leaf 10753) (.leaf 10771))))))
  (.branch 1328 (.branch 1320 (.branch 1316 (.branch 1314 (.branch 1313 (.leaf 10781) (.leaf 10789))
  (.branch 1315 (.leaf 10799) (.leaf 10831))) (.branch 1318 (.branch 1317 (.leaf 10837) (.leaf
  10847)) (.branch 1319 (.leaf 10853) (.leaf 10859)))) (.branch 1324 (.branch 1322 (.branch 1321
  (.leaf 10861) (.leaf 10867)) (.branch 1323 (.leaf 10883) (.leaf 10889))) (.branch 1326 (.branch
  1325 (.leaf 10891) (.leaf 10903)) (.branch 1327 (.leaf 10909) (.leaf 10937))))) (.branch 1336
  (.branch 1332 (.branch 1330 (.branch 1329 (.leaf 10939) (.leaf 10949)) (.branch 1331 (.leaf 10957)
  (.leaf 10973))) (.branch 1334 (.branch 1333 (.leaf 10979) (.leaf 10987)) (.branch 1335 (.leaf
  10993) (.leaf 11003)))) (.branch 1340 (.branch 1338 (.branch 1337 (.leaf 11027) (.leaf 11047))
  (.branch 1339 (.leaf 11057) (.leaf 11059))) (.branch 1342 (.branch 1341 (.leaf 11069) (.leaf
  11071)) (.branch 1343 (.leaf 11083) (.leaf 11087))))))) (.branch 1376 (.branch 1360 (.branch 1352
  (.branch 1348 (.branch 1346 (.branch 1345 (.leaf 11093) (.leaf 11113)) (.branch 1347 (.leaf 11117)
  (.leaf 11119))) (.branch 1350 (.branch 1349 (.leaf 11131) (.leaf 11149)) (.branch 1351 (.leaf
  11159) (.leaf 11161)))) (.branch 1356 (.branch 1354 (.branch 1353 (.leaf 11171) (.leaf 11173))
  (.branch 1355 (.leaf 11177) (.leaf 11197))) (.branch 1358 (.branch 1357 (.leaf 11213) (.leaf
  11239)) (.branch 1359 (.leaf 11243) (.leaf 11251))))) (.branch 1368 (.branch 1364 (.branch 1362
  (.branch 1361 (.leaf 11257) (.leaf 11261)) (.branch 1363 (.leaf 11273) (.leaf 11279))) (.branch
  1366 (.branch 1365 (.leaf 11287) (.leaf 11299)) (.branch 1367 (.leaf 11311) (.leaf 11317))))
  (.branch 1372 (.branch 1370 (.branch 1369 (.leaf 11321) (.leaf 11329)) (.branch 1371 (.leaf 11351)
  (.leaf 11353))) (.branch 1374 (.branch 1373 (.leaf 11369) (.leaf 11383)) (.branch 1375 (.leaf
  11393) (.leaf 11399)))))) (.branch 1392 (.branch 1384 (.branch 1380 (.branch 1378 (.branch 1377
  (.leaf 11411) (.leaf 11423)) (.branch 1379 (.leaf 11437) (.leaf 11443))) (.branch 1382 (.branch
  1381 (.leaf 11447) (.leaf 11467)) (.branch 1383 (.leaf 11471) (.leaf 11483)))) (.branch 1388
  (.branch 1386 (.branch 1385 (.leaf 11489) (.leaf 11491)) (.branch 1387 (.leaf 11497) (.leaf
  11503))) (.branch 1390 (.branch 1389 (.leaf 11519) (.leaf 11527)) (.branch 1391 (.leaf 11549)
  (.leaf 11551))))) (.branch 1400 (.branch 1396 (.branch 1394 (.branch 1393 (.leaf 11579) (.leaf
  11587)) (.branch 1395 (.leaf 11593) (.leaf 11597))) (.branch 1398 (.branch 1397 (.leaf 11617)
  (.leaf 11621)) (.branch 1399 (.leaf 11633) (.leaf 11657)))) (.branch 1404 (.branch 1402 (.branch
  1401 (.leaf 11677) (.leaf 11681)) (.branch 1403 (.leaf 11689) (.leaf 11699))) (.branch 1406
  (.branch 1405 (.leaf 11701) (.leaf 11717)) (.branch 1407 (.leaf 11719) (.leaf 11731))))))))
  (.branch 1472 (.branch 1440 (.branch 1424 (.branch 1416 (.branch 1412 (.branch 1410 (.branch 1409
  (.leaf 11743) (.leaf 11777)) (.branch 1411 (.leaf 11779) (.leaf 11783))) (.branch 1414 (.branch
  1413 (.leaf 11789) (.leaf 11801)) (.branch 1415 (.leaf 11807) (.leaf 11813)))) (.branch 1420
  (.branch 1418 (.branch 1417 (.leaf 11821) (.leaf 11827)) (.branch 1419 (.leaf 11831) (.leaf
  11833))) (.branch 1422 (.branch 1421 (.leaf 11839) (.leaf 11863)) (.branch 1423 (.leaf 11867)
  (.leaf 11887))))) (.branch 1432 (.branch 1428 (.branch 1426 (.branch 1425 (.leaf 11897) (.leaf
  11903)) (.branch 1427 (.leaf 11909) (.leaf 11923))) (.branch 1430 (.branch 1429 (.leaf 11927)
  (.leaf 11933)) (.branch 1431 (.leaf 11939) (.leaf 11941)))) (.branch 1436 (.branch 1434 (.branch
  1433 (.leaf 11953) (.leaf 11959)) (.branch 1435 (.leaf 11969) (.leaf 11971))) (.branch 1438
  (.branch 1437 (.leaf 11981) (.leaf 11987)) (.branch 1439 (.leaf 12007) (.leaf 12011)))))) (.branch
  1456 (.branch 1448 (.branch 1444 (.branch 1442 (.branch 1441 (.leaf 12037) (.leaf 12041)) (.branch
  1443 (.leaf 12043) (.leaf 12049))) (.branch 1446 (.branch 1445 (.leaf 12071) (.leaf 12073))
  (.branch 1447 (.leaf 12097) (.leaf 12101)))) (.branch 1452 (.branch 1450 (.branch 1449 (.leaf
  12107) (.leaf 12109)) (.branch 1451 (.leaf 12113) (.leaf 12119))) (.branch 1454 (.branch 1453
  (.leaf 12143) (.leaf 12149)) (.branch 1455 (.leaf 12157) (.leaf 12161))))) (.branch 1464 (.branch
  1460 (.branch 1458 (.branch 1457 (.leaf 12163) (.leaf 12197)) (.branch 1459 (.leaf 12203) (.leaf
  12211))) (.branch 1462 (.branch 1461 (.leaf 12227) (.leaf 12239)) (.branch 1463 (.leaf 12241)
  (.leaf 12251)))) (.branch 1468 (.branch 1466 (.branch 1465 (.leaf 12253) (.leaf 12263)) (.branch
  1467 (.leaf 12269) (.leaf 12277))) (.branch 1470 (.branch 1469 (.leaf 12281) (.leaf 12289))
  (.branch 1471 (.leaf 12301) (.leaf 12323))))))) (.branch 1504 (.branch 1488 (.branch 1480 (.branch
  1476 (.branch 1474 (.branch 1473 (.leaf 12329) (.leaf 12343)) (.branch 1475 (.leaf 12347) (.leaf
  12373))) (.branch 1478 (.branch 1477 (.leaf 12377) (.leaf 12379)) (.branch 1479 (.leaf 12391)
  (.leaf 12401)))) (.branch 1484 (.branch 1482 (.branch 1481 (.leaf 12409) (.leaf 12413)) (.branch
  1483 (.leaf 12421) (.leaf 12433))) (.branch 1486 (.branch 1485 (.leaf 12437) (.leaf 12451))
  (.branch 1487 (.leaf 12457) (.leaf 12473))))) (.branch 1496 (.branch 1492 (.branch 1490 (.branch
  1489 (.leaf 12479) (.leaf 12487)) (.branch 1491 (.leaf 12491) (.leaf 12497))) (.branch 1494
  (.branch 1493 (.leaf 12503) (.leaf 12511)) (.branch 1495 (.leaf 12517) (.leaf 12527)))) (.branch
  1500 (.branch 1498 (.branch 1497 (.leaf 12539) (.leaf 12541)) (.branch 1499 (.leaf 12547) (.leaf
  12553))) (.branch 1502 (.branch 1501 (.leaf 12569) (.leaf 12577)) (.branch 1503 (.leaf 12583)
  (.leaf 12589)))))) (.branch 1520 (.branch 1512 (.branch 1508 (.branch 1506 (.branch 1505 (.leaf
  12601) (.leaf 12611)) (.branch 1507 (.leaf 12613) (.leaf 12619))) (.branch 1510 (.branch 1509
  (.leaf 12637) (.leaf 12641)) (.branch 1511 (.leaf 12647) (.leaf 12653)))) (.branch 1516 (.branch
  1514 (.branch 1513 (.leaf 12659) (.leaf 12671)) (.branch 1515 (.leaf 12689) (.leaf 12697)))
  (.branch 1518 (.branch 1517 (.leaf 12703) (.leaf 12713)) (.branch 1519 (.leaf 12721) (.leaf
  12739))))) (.branch 1528 (.branch 1524 (.branch 1522 (.branch 1521 (.leaf 12743) (.leaf 12757))
  (.branch 1523 (.leaf 12763) (.leaf 12781))) (.branch 1526 (.branch 1525 (.leaf 12791) (.leaf
  12799)) (.branch 1527 (.leaf 12809) (.leaf 12821)))) (.branch 1532 (.branch 1530 (.branch 1529
  (.leaf 12823) (.leaf 12829)) (.branch 1531 (.leaf 12841) (.leaf 12853))) (.branch 1534 (.branch
  1533 (.leaf 12889) (.leaf 12893)) (.branch 1535 (.leaf 12899) (.leaf 12907)))))))))) (.branch 1792
  (.branch 1664 (.branch 1600 (.branch 1568 (.branch 1552 (.branch 1544 (.branch 1540 (.branch 1538
  (.branch 1537 (.leaf 12911) (.leaf 12917)) (.branch 1539 (.leaf 12919) (.leaf 12923))) (.branch
  1542 (.branch 1541 (.leaf 12941) (.leaf 12953)) (.branch 1543 (.leaf 12959) (.leaf 12967))))
  (.branch 1548 (.branch 1546 (.branch 1545 (.leaf 12973) (.leaf 12979)) (.branch 1547 (.leaf 12983)
  (.leaf 13001))) (.branch 1550 (.branch 1549 (.leaf 13003) (.leaf 13007)) (.branch 1551 (.leaf
  13009) (.leaf 13033))))) (.branch 1560 (.branch 1556 (.branch 1554 (.branch 1553 (.leaf 13037)
  (.leaf 13043)) (.branch 1555 (.leaf 13049) (.leaf 13063))) (.branch 1558 (.branch 1557 (.leaf
  13093) (.leaf 13099)) (.branch 1559 (.leaf 13103) (.leaf 13109)))) (.branch 1564 (.branch 1562
  (.branch 1561 (.leaf 13121) (.leaf 13127)) (.branch 1563 (.leaf 13147) (.leaf 13151))) (.branch
  1566 (.branch 1565 (.leaf 13159) (.leaf 13163)) (.branch 1567 (.leaf 13171) (.leaf 13177))))))
  (.branch 1584 (.branch 1576 (.branch 1572 (.branch 1570 (.branch 1569 (.leaf 13183) (.leaf 13187))
  (.branch 1571 (.leaf 13217) (.leaf 13219))) (.branch 1574 (.branch 1573 (.leaf 13229) (.leaf
  13241)) (.branch 1575 (.leaf 13249) (.leaf 13259)))) (.branch 1580 (.branch 1578 (.branch 1577
  (.leaf 13267) (.leaf 13291)) (.branch 1579 (.leaf 13297) (.leaf 13309))) (.branch 1582 (.branch
  1581 (.leaf 13313) (.leaf 13327)) (.branch 1583 (.leaf 13331) (.leaf 13337))))) (.branch 1592
  (.branch 1588 (.branch 1586 (.branch 1585 (.leaf 13339) (.leaf 13367)) (.branch 1587 (.leaf 13381)
  (.leaf 13397))) (.branch 1590 (.branch 1589 (.leaf 13399) (.leaf 13411)) (.branch 1591 (.leaf
  13417) (.leaf 13421)))) (.branch 1596 (.branch 1594 (.branch 1593 (.leaf 13441) (.leaf 13451))
  (.branch 1595 (.leaf 13457) (.leaf 13463))) (.branch 1598 (.branch 1597 (.leaf 13469) (.leaf
  13477)) (.branch 1599 (.leaf 13487) (.leaf 13499))))))) (.branch 1632 (.branch 1616 (.branch 1608
  (.branch 1604 (.branch 1602 (.branch 1601 (.leaf 13513) (.leaf 13523)) (.branch 1603 (.leaf 13537)
  (.leaf 13553))) (.branch 1606 (.branch 1605 (.leaf 13567) (.leaf 13577)) (.branch 1607 (.leaf
  13591) (.leaf 13597)))) (.branch 1612 (.branch 1610 (.branch 1609 (.leaf 13613) (.leaf 13619))
  (.branch 1611 (.leaf 13627) (.leaf 13633))) (.branch 1614 (.branch 1613 (.leaf 13649) (.leaf
  13669)) (.branch 1615 (.leaf 13679) (.leaf 13681))))) (.branch 1624 (.branch 1620 (.branch 1618
  (.branch 1617 (.leaf 13687) (.leaf 13691)) (.branch 1619 (.leaf 13693) (.leaf 13697))) (.branch
  1622 (.branch 1621 (.leaf 13709) (.leaf 13711)) (.branch 1623 (.leaf 13721) (.leaf 13723))))
  (.branch 1628 (.branch 1626 (.branch 1625 (.leaf 13729) (.leaf 13751)) (.branch 1627 (.leaf 13757)
  (.leaf 13759))) (.branch 1630 (.branch 1629 (.leaf 13763) (.leaf 13781)) (.branch 1631 (.leaf
  13789) (.leaf 13799)))))) (.branch 1648 (.branch 1640 (.branch 1636 (.branch 1634 (.branch 1633
  (.leaf 13807) (.leaf 13829)) (.branch 1635 (.leaf 13831) (.leaf 13841))) (.branch 1638 (.branch
  1637 (.leaf 13859) (.leaf 13873)) (.branch 1639 (.leaf 13877) (.leaf 13879)))) (.branch 1644
  (.branch 1642 (.branch 1641 (.leaf 13883) (.leaf 13901)) (.branch 1643 (.leaf 13903) (.leaf
  13907))) (.branch 1646 (.branch 1645 (.leaf 13913) (.leaf 13921)) (.branch 1647 (.leaf 13931)
  (.leaf 13933))))) (.branch 1656 (.branch 1652 (.branch 1650 (.branch 1649 (.leaf 13963) (.leaf
  13967)) (.branch 1651 (.leaf 13997) (.leaf 13999))) (.branch 1654 (.branch 1653 (.leaf 14009)
  (.leaf 14011)) (.branch 1655 (.leaf 14029) (.leaf 14033)))) (.branch 1660 (.branch 1658 (.branch
  1657 (.leaf 14051) (.leaf 14057)) (.branch 1659 (.leaf 14071) (.leaf 14081))) (.branch 1662
  (.branch 1661 (.leaf 14083) (.leaf 14087)) (.branch 1663 (.leaf 14107) (.leaf 14143))))))))
  (.branch 1728 (.branch 1696 (.branch 1680 (.branch 1672 (.branch 1668 (.branch 1666 (.branch 1665
  (.leaf 14149) (.leaf 14153)) (.branch 1667 (.leaf 14159) (.leaf 14173))) (.branch 1670 (.branch
  1669 (.leaf 14177) (.leaf 14197)) (.branch 1671 (.leaf 14207) (.leaf 14221)))) (.branch 1676
  (.branch 1674 (.branch 1673 (.leaf 14243) (.leaf 14249)) (.branch 1675 (.leaf 14251) (.leaf
  14281))) (.branch 1678 (.branch 1677 (.leaf 14293) (.leaf 14303)) (.branch 1679 (.leaf 14321)
  (.leaf 14323))))) (.branch 1688 (.branch 1684 (.branch 1682 (.branch 1681 (.leaf 14327) (.leaf
  14341)) (.branch 1683 (.leaf 14347) (.leaf 14369))) (.branch 1686 (.branch 1685 (.leaf 14387)
  (.leaf 14389)) (.branch 1687 (.leaf 14401) (.leaf 14407)))) (.branch 1692 (.branch 1690 (.branch
  1689 (.leaf 14411) (.leaf 14419)) (.branch 1691 (.leaf 14423) (.leaf 14431))) (.branch 1694
  (.branch 1693 (.leaf 14437) (.leaf 14447)) (.branch 1695 (.leaf 14449) (.leaf 14461)))))) (.branch
  1712 (.branch 1704 (.branch 1700 (.branch 1698 (.branch 1697 (.leaf 14479) (.leaf 14489)) (.branch
  1699 (.leaf 14503) (.leaf 14519))) (.branch 1702 (.branch 1701 (.leaf 14533) (.leaf 14537))
  (.branch 1703 (.leaf 14543) (.leaf 14549)))) (.branch 1708 (.branch 1706 (.branch 1705 (.leaf
  14551) (.leaf 14557)) (.branch 1707 (.leaf 14561) (.leaf 14563))) (.branch 1710 (.branch 1709
  (.leaf 14591) (.leaf 14593)) (.branch 1711 (.leaf 14621) (.leaf 14627))))) (.branch 1720 (.branch
  1716 (.branch 1714 (.branch 1713 (.leaf 14629) (.leaf 14633)) (.branch 1715 (.leaf 14639) (.leaf
  14653))) (.branch 1718 (.branch 1717 (.leaf 14657) (.leaf 14669)) (.branch 1719 (.leaf 14683)
  (.leaf 14699)))) (.branch 1724 (.branch 1722 (.branch 1721 (.leaf 14713) (.leaf 14717)) (.branch
  1723 (.leaf 14723) (.leaf 14731))) (.branch 1726 (.branch 1725 (.leaf 14737) (.leaf 14741))
  (.branch 1727 (.leaf 14747) (.leaf 14753))))))) (.branch 1760 (.branch 1744 (.branch 1736 (.branch
  1732 (.branch 1730 (.branch 1729 (.leaf 14759) (.leaf 14767)) (.branch 1731 (.leaf 14771) (.leaf
  14779))) (.branch 1734 (.branch 1733 (.leaf 14783) (.leaf 14797)) (.branch 1735 (.leaf 14813)
  (.leaf 14821)))) (.branch 1740 (.branch 1738 (.branch 1737 (.leaf 14827) (.leaf 14831)) (.branch
  1739 (.leaf 14843) (.leaf 14851))) (.branch 1742 (.branch 1741 (.leaf 14867) (.leaf 14869))
  (.branch 1743 (.leaf 14879) (.leaf 14887))))) (.branch 1752 (.branch 1748 (.branch 1746 (.branch
  1745 (.leaf 14891) (.leaf 14897)) (.branch 1747 (.leaf 14923) (.leaf 14929))) (.branch 1750
  (.branch 1749 (.leaf 14939) (.leaf 14947)) (.branch 1751 (.leaf 14951) (.leaf 14957)))) (.branch
  1756 (.branch 1754 (.branch 1753 (.leaf 14969) (.leaf 14983)) (.branch 1755 (.leaf 15013) (.leaf
  15017))) (.branch 1758 (.branch 1757 (.leaf 15031) (.leaf 15053)) (.branch 1759 (.leaf 15061)
  (.leaf 15073)))))) (.branch 1776 (.branch 1768 (.branch 1764 (.branch 1762 (.branch 1761 (.leaf
  15077) (.leaf 15083)) (.branch 1763 (.leaf 15091) (.leaf 15101))) (.branch 1766 (.branch 1765
  (.leaf 15107) (.leaf 15121)) (.branch 1767 (.leaf 15131) (.leaf 15137)))) (.branch 1772 (.branch
  1770 (.branch 1769 (.leaf 15139) (.leaf 15149)) (.branch 1771 (.leaf 15161) (.leaf 15173)))
  (.branch 1774 (.branch 1773 (.leaf 15187) (.leaf 15193)) (.branch 1775 (.leaf 15199) (.leaf
  15217))))) (.branch 1784 (.branch 1780 (.branch 1778 (.branch 1777 (.leaf 15227) (.leaf 15233))
  (.branch 1779 (.leaf 15241) (.leaf 15259))) (.branch 1782 (.branch 1781 (.leaf 15263) (.leaf
  15269)) (.branch 1783 (.leaf 15271) (.leaf 15277)))) (.branch 1788 (.branch 1786 (.branch 1785
  (.leaf 15287) (.leaf 15289)) (.branch 1787 (.leaf 15299) (.leaf 15307))) (.branch 1790 (.branch
  1789 (.leaf 15313) (.leaf 15319)) (.branch 1791 (.leaf 15329) (.leaf 15331))))))))) (.branch 1920
  (.branch 1856 (.branch 1824 (.branch 1808 (.branch 1800 (.branch 1796 (.branch 1794 (.branch 1793
  (.leaf 15349) (.leaf 15359)) (.branch 1795 (.leaf 15361) (.leaf 15373))) (.branch 1798 (.branch
  1797 (.leaf 15377) (.leaf 15383)) (.branch 1799 (.leaf 15391) (.leaf 15401)))) (.branch 1804
  (.branch 1802 (.branch 1801 (.leaf 15413) (.leaf 15427)) (.branch 1803 (.leaf 15439) (.leaf
  15443))) (.branch 1806 (.branch 1805 (.leaf 15451) (.leaf 15461)) (.branch 1807 (.leaf 15467)
  (.leaf 15473))))) (.branch 1816 (.branch 1812 (.branch 1810 (.branch 1809 (.leaf 15493) (.leaf
  15497)) (.branch 1811 (.leaf 15511) (.leaf 15527))) (.branch 1814 (.branch 1813 (.leaf 15541)
  (.leaf 15551)) (.branch 1815 (.leaf 15559) (.leaf 15569)))) (.branch 1820 (.branch 1818 (.branch
  1817 (.leaf 15581) (.leaf 15583)) (.branch 1819 (.leaf 15601) (.leaf 15607))) (.branch 1822
  (.branch 1821 (.leaf 15619) (.leaf 15629)) (.branch 1823 (.leaf 15641) (.leaf 15643)))))) (.branch
  1840 (.branch 1832 (.branch 1828 (.branch 1826 (.branch 1825 (.leaf 15647) (.leaf 15649)) (.branch
  1827 (.leaf 15661) (.leaf 15667))) (.branch 1830 (.branch 1829 (.leaf 15671) (.leaf 15679))
  (.branch 1831 (.leaf 15683) (.leaf 15727)))) (.branch 1836 (.branch 1834 (.branch 1833 (.leaf
  15731) (.leaf 15733)) (.branch 1835 (.leaf 15737) (.leaf 15739))) (.branch 1838 (.branch 1837
  (.leaf 15749) (.leaf 15761)) (.branch 1839 (.leaf 15767) (.leaf 15773))))) (.branch 1848 (.branch
  1844 (.branch 1842 (.branch 1841 (.leaf 15787) (.leaf 15791)) (.branch 1843 (.leaf 15797) (.leaf
  15803))) (.branch 1846 (.branch 1845 (.leaf 15809) (.leaf 15817)) (.branch 1847 (.leaf 15823)
  (.leaf 15859)))) (.branch 1852 (.branch 1850 (.branch 1849 (.leaf 15877) (.leaf 15881)) (.branch
  1851 (.leaf 15887) (.leaf 15889))) (.branch 1854 (.branch 1853 (.leaf 15901) (.leaf 15907))
  (.branch 1855 (.leaf 15913) (.leaf 15919))))))) (.branch 1888 (.branch 1872 (.branch 1864 (.branch
  1860 (.branch 1858 (.branch 1857 (.leaf 15923) (.leaf 15937)) (.branch 1859 (.leaf 15959) (.leaf
  15971))) (.branch 1862 (.branch 1861 (.leaf 15973) (.leaf 15991)) (.branch 1863 (.leaf 16001)
  (.leaf 16007)))) (.branch 1868 (.branch 1866 (.branch 1865 (.leaf 16033) (.leaf 16057)) (.branch
  1867 (.leaf 16061) (.leaf 16063))) (.branch 1870 (.branch 1869 (.leaf 16067) (.leaf 16069))
  (.branch 1871 (.leaf 16073) (.leaf 16087))))) (.branch 1880 (.branch 1876 (.branch 1874 (.branch
  1873 (.leaf 16091) (.leaf 16097)) (.branch 1875 (.leaf 16103) (.leaf 16111))) (.branch 1878
  (.branch 1877 (.leaf 16127) (.leaf 16139)) (.branch 1879 (.leaf 16141) (.leaf 16183)))) (.branch
  1884 (.branch 1882 (.branch 1881 (.leaf 16187) (.leaf 16189)) (.branch 1883 (.leaf 16193) (.leaf
  16217))) (.branch 1886 (.branch 1885 (.leaf 16223) (.leaf 16229)) (.branch 1887 (.leaf 16231)
  (.leaf 16249)))))) (.branch 1904 (.branch 1896 (.branch 1892 (.branch 1890 (.branch 1889 (.leaf
  16253) (.leaf 16267)) (.branch 1891 (.leaf 16273) (.leaf 16301))) (.branch 1894 (.branch 1893
  (.leaf 16319) (.leaf 16333)) (.branch 1895 (.leaf 16339) (.leaf 16349)))) (.branch 1900 (.branch
  1898 (.branch 1897 (.leaf 16361) (.leaf 16363)) (.branch 1899 (.leaf 16369) (.leaf 16381)))
  (.branch 1902 (.branch 1901 (.leaf 16411) (.leaf 16417)) (.branch 1903 (.leaf 16421) (.leaf
  16427))))) (.branch 1912 (.branch 1908 (.branch 1906 (.branch 1905 (.leaf 16433) (.leaf 16447))
  (.branch 1907 (.leaf 16451) (.leaf 16453))) (.branch 1910 (.branch 1909 (.leaf 16477) (.leaf
  16481)) (.branch 1911 (.leaf 16487) (.leaf 16493)))) (.branch 1916 (.branch 1914 (.branch 1913
  (.leaf 16519) (.leaf 16529)) (.branch 1915 (.leaf 16547) (.leaf 16553))) (.branch 1918 (.branch
  1917 (.leaf 16561) (.leaf 16567)) (.branch 1919 (.leaf 16573) (.leaf 16603)))))))) (.branch 1984
  (.branch 1952 (.branch 1936 (.branch 1928 (.branch 1924 (.branch 1922 (.branch 1921 (.leaf 16607)
  (.leaf 16619)) (.branch 1923 (.leaf 16631) (.leaf 16633))) (.branch 1926 (.branch 1925 (.leaf
  16649) (.leaf 16651)) (.branch 1927 (.leaf 16657) (.leaf 16661)))) (.branch 1932 (.branch 1930
  (.branch 1929 (.leaf 16673) (.leaf 16691)) (.branch 1931 (.leaf 16693) (.leaf 16699))) (.branch
  1934 (.branch 1933 (.leaf 16703) (.leaf 16729)) (.branch 1935 (.leaf 16741) (.leaf 16747)))))
  (.branch 1944 (.branch 1940 (.branch 1938 (.branch 1937 (.leaf 16759) (.leaf 16763)) (.branch 1939
  (.leaf 16787) (.leaf 16811))) (.branch 1942 (.branch 1941 (.leaf 16823) (.leaf 16829)) (.branch
  1943 (.leaf 16831) (.leaf 16843)))) (.branch 1948 (.branch 1946 (.branch 1945 (.leaf 16871) (.leaf
  16879)) (.branch 1947 (.leaf 16883) (.leaf 16889))) (.branch 1950 (.branch 1949 (.leaf 16901)
  (.leaf 16903)) (.branch 1951 (.leaf 16921) (.leaf 16927)))))) (.branch 1968 (.branch 1960 (.branch
  1956 (.branch 1954 (.branch 1953 (.leaf 16931) (.leaf 16937)) (.branch 1955 (.leaf 16943) (.leaf
  16963))) (.branch 1958 (.branch 1957 (.leaf 16979) (.leaf 16981)) (.branch 1959 (.leaf 16987)
  (.leaf 16993)))) (.branch 1964 (.branch 1962 (.branch 1961 (.leaf 17011) (.leaf 17021)) (.branch
  1963 (.leaf 17027) (.leaf 17029))) (.branch 1966 (.branch 1965 (.leaf 17033) (.leaf 17041))
  (.branch 1967 (.leaf 17047) (.leaf 17053))))) (.branch 1976 (.branch 1972 (.branch 1970 (.branch
  1969 (.leaf 17077) (.leaf 17093)) (.branch 1971 (.leaf 17099) (.leaf 17107))) (.branch 1974
  (.branch 1973 (.leaf 17117) (.leaf 17123)) (.branch 1975 (.leaf 17137) (.leaf 17159)))) (.branch
  1980 (.branch 1978 (.branch 1977 (.leaf 17167) (.leaf 17183)) (.branch 1979 (.leaf 17189) (.leaf
  17191))) (.branch 1982 (.branch 1981 (.leaf 17203) (.leaf 17207)) (.branch 1983 (.leaf 17209)
  (.leaf 17231))))))) (.branch 2016 (.branch 2000 (.branch 1992 (.branch 1988 (.branch 1986 (.branch
  1985 (.leaf 17239) (.leaf 17257)) (.branch 1987 (.leaf 17291) (.leaf 17293))) (.branch 1990
  (.branch 1989 (.leaf 17299) (.leaf 17317)) (.branch 1991 (.leaf 17321) (.leaf 17327)))) (.branch
  1996 (.branch 1994 (.branch 1993 (.leaf 17333) (.leaf 17341)) (.branch 1995 (.leaf 17351) (.leaf
  17359))) (.branch 1998 (.branch 1997 (.leaf 17377) (.leaf 17383)) (.branch 1999 (.leaf 17387)
  (.leaf 17389))))) (.branch 2008 (.branch 2004 (.branch 2002 (.branch 2001 (.leaf 17393) (.leaf
  17401)) (.branch 2003 (.leaf 17417) (.leaf 17419))) (.branch 2006 (.branch 2005 (.leaf 17431)
  (.leaf 17443)) (.branch 2007 (.leaf 17449) (.leaf 17467)))) (.branch 2012 (.branch 2010 (.branch
  2009 (.leaf 17471) (.leaf 17477)) (.branch 2011 (.leaf 17483) (.leaf 17489))) (.branch 2014
  (.branch 2013 (.leaf 17491) (.leaf 17497)) (.branch 2015 (.leaf 17509) (.leaf 17519)))))) (.branch
  2032 (.branch 2024 (.branch 2020 (.branch 2018 (.branch 2017 (.leaf 17539) (.leaf 17551)) (.branch
  2019 (.leaf 17569) (.leaf 17573))) (.branch 2022 (.branch 2021 (.leaf 17579) (.leaf 17581))
  (.branch 2023 (.leaf 17597) (.leaf 17599)))) (.branch 2028 (.branch 2026 (.branch 2025 (.leaf
  17609) (.leaf 17623)) (.branch 2027 (.leaf 17627) (.leaf 17657))) (.branch 2030 (.branch 2029
  (.leaf 17659) (.leaf 17669)) (.branch 2031 (.leaf 17681) (.leaf 17683))))) (.branch 2040 (.branch
  2036 (.branch 2034 (.branch 2033 (.leaf 17707) (.leaf 17713)) (.branch 2035 (.leaf 17729) (.leaf
  17737))) (.branch 2038 (.branch 2037 (.leaf 17747) (.leaf 17749)) (.branch 2039 (.leaf 17761)
  (.leaf 17783)))) (.branch 2044 (.branch 2042 (.branch 2041 (.leaf 17789) (.leaf 17791)) (.branch
  2043 (.leaf 17807) (.leaf 17827))) (.branch 2046 (.branch 2045 (.leaf 17837) (.leaf 17839))
  (.branch 2047 (.leaf 17851) (.leaf 17863))))))))))))

/-- The primes as a list (index `i` ↦ `primeArr.get i`). -/
def primes : List Nat := (List.range 2048).map primeArr.get

def primeOf (x : Nat) : Nat := primeArr.get x

theorem primeArr_get (x : Nat) (hx : x < 2048) : primeArr.get x = primes.getD x 0 := by
  simp [primes, List.getD_eq_getElem?_getD, hx]

/-- Negate when the sign flag is set. -/
noncomputable def sgn (md : Nat) (s : Bool) (p : P) : P := Bool.rec p (pneg md p) s

/-- Summands of `±e` prepended to `acc` (`s = true` means `-e`): additive chains are flattened so
that they can be summed by balanced merging. -/
noncomputable def terms (md : Nat) (e : Expr) : Bool → List P → List P :=
  Expr.rec (motive := fun _ => Bool → List P → List P)
    (fun k s acc => sgn md s (pconst md k) :: acc)
    (fun k s acc => sgn md s (pconst md k) :: acc)
    (fun k s acc => sgn md s (pconst md k) :: acc)
    (fun x s acc => sgn md s (.cons 1 (primeOf x) .nil) :: acc)
    (fun _ ih s acc => idL (ih (!s) acc))
    (fun _ _ ih₁ ih₂ s acc => idL (ih₁ s (ih₂ s acc)))
    (fun _ _ ih₁ ih₂ s acc => idL (ih₁ s (ih₂ (!s) acc)))
    (fun _ _ ih₁ ih₂ s acc =>
      sgn md s (pmul md (sumAll md 64 (ih₁ false [])) (sumAll md 64 (ih₂ false []))) :: acc)
    (fun a k ih s acc => sgn md s (Bool.rec
      (Expr.rec (motive := fun _ => P) (fun _ => ppow md (sumAll md 64 (ih false [])) k)
        (fun _ => ppow md (sumAll md 64 (ih false [])) k)
        (fun _ => ppow md (sumAll md 64 (ih false [])) k)
        (fun x => .cons 1 (Nat.pow (primeOf x) k) .nil)
        (fun _ _ => ppow md (sumAll md 64 (ih false [])) k)
        (fun _ _ _ _ => ppow md (sumAll md 64 (ih false [])) k)
        (fun _ _ _ _ => ppow md (sumAll md 64 (ih false [])) k)
        (fun _ _ _ _ => ppow md (sumAll md 64 (ih false [])) k)
        (fun _ _ _ => ppow md (sumAll md 64 (ih false [])) k) a)
      (.cons 1 1 .nil) (Nat.beq k 0)) :: acc)
    e

noncomputable def norm (md : Nat) (e : Expr) : P := sumAll md 64 (terms md e false [])

/-- every variable index of `e` is `< n` -/
def VOk (n : Nat) : Expr → Prop
  | .var x => x < n
  | .neg a => VOk n a
  | .add a b => VOk n a ∧ VOk n b
  | .sub a b => VOk n a ∧ VOk n b
  | .mul a b => VOk n a ∧ VOk n b
  | .pow a _ => VOk n a
  | _ => True

/-- Kernel check of `VOk n e ∧ acc` (accumulator style, so that long additive chains are walked
iteratively rather than by deep recursion). -/
noncomputable def varsLtA (n : Nat) (e : Expr) : Bool → Bool :=
  Expr.rec (motive := fun _ => Bool → Bool)
    (fun _ acc => idB acc) (fun _ acc => idB acc) (fun _ acc => idB acc)
    (fun x acc => Bool.rec false (idB acc) (Nat.blt x n))
    (fun _ ih acc => idB (ih acc))
    (fun _ _ ih₁ ih₂ acc => idB (ih₁ (ih₂ acc)))
    (fun _ _ ih₁ ih₂ acc => idB (ih₁ (ih₂ acc)))
    (fun _ _ ih₁ ih₂ acc => idB (ih₁ (ih₂ acc)))
    (fun _ _ ih acc => idB (ih acc))
    e

theorem varsLtA_iff (n : Nat) : ∀ (e : Expr) (acc : Bool),
    varsLtA n e acc = true ↔ VOk n e ∧ acc = true
  | .num _, acc => by simp [varsLtA, VOk, idB]
  | .natCast _, acc => by simp [varsLtA, VOk, idB]
  | .intCast _, acc => by simp [varsLtA, VOk, idB]
  | .var x, acc => by
    show Bool.rec false (idB acc) (Nat.blt x n) = true ↔ x < n ∧ acc = true
    cases h : Nat.blt x n
    · have : ¬ x < n := by rw [← Nat.blt_eq]; simp [h]
      simp [this]
    · have : x < n := by rw [← Nat.blt_eq]; exact h
      simp [this, idB]
  | .neg a, acc => by
    show idB (varsLtA n a acc) = true ↔ VOk n a ∧ acc = true
    rw [idB]; exact varsLtA_iff n a acc
  | .add a b, acc => by
    show idB (varsLtA n a (varsLtA n b acc)) = true ↔ (VOk n a ∧ VOk n b) ∧ acc = true
    rw [idB]
    rw [varsLtA_iff n a, varsLtA_iff n b]; tauto
  | .sub a b, acc => by
    show idB (varsLtA n a (varsLtA n b acc)) = true ↔ (VOk n a ∧ VOk n b) ∧ acc = true
    rw [idB]
    rw [varsLtA_iff n a, varsLtA_iff n b]; tauto
  | .mul a b, acc => by
    show idB (varsLtA n a (varsLtA n b acc)) = true ↔ (VOk n a ∧ VOk n b) ∧ acc = true
    rw [idB]
    rw [varsLtA_iff n a, varsLtA_iff n b]; tauto
  | .pow a _, acc => by
    show idB (varsLtA n a acc) = true ↔ VOk n a ∧ acc = true
    rw [idB]; exact varsLtA_iff n a acc

noncomputable def isNil (p : P) : Bool := P.rec (motive := fun _ => Bool) true (fun _ _ _ _ => false) p

noncomputable def check (md : Nat) (e : Expr) : Bool := (varsLtA 2048 e true).and (isNil (norm md e))

/-! ### Soundness -/

section Sound
variable {α : Type*} [CommRing α] (v : Nat → α)

def mdenL : List Nat → Nat → Nat → α
  | [], _, _ => 1
  | p :: ps, i, m => v i ^ (m.factorization p) * mdenL ps (i + 1) m

open Classical in
noncomputable def mden (m : Nat) : α := if m = 0 then 0 else mdenL v primes 0 m

theorem mdenL_mul (m n : Nat) (hm : m ≠ 0) (hn : n ≠ 0) :
    ∀ (ps : List Nat) (i : Nat), mdenL v ps i (m * n) = mdenL v ps i m * mdenL v ps i n
  | [], i => by simp [mdenL]
  | p :: ps, i => by
    simp only [mdenL, Nat.factorization_mul hm hn, Finsupp.add_apply, pow_add,
      mdenL_mul m n hm hn ps (i + 1)]
    ring

theorem mden_mul (m n : Nat) : mden v (m * n) = mden v m * mden v n := by
  unfold mden
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [hm, hn, mdenL_mul v m n hm hn]

theorem mdenL_of_fact_zero (m : Nat) :
    ∀ (ps : List Nat) (i : Nat), (∀ q ∈ ps, m.factorization q = 0) → mdenL v ps i m = 1
  | [], _, _ => rfl
  | p :: ps, i, h => by
    simp only [mdenL, h p List.mem_cons_self, pow_zero, one_mul]
    exact mdenL_of_fact_zero m ps (i + 1) (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem mden_one : mden v 1 = (1 : α) := by
  unfold mden
  simp only [one_ne_zero, ite_false]
  exact mdenL_of_fact_zero v 1 _ 0 (fun q _ => by simp)

theorem mden_pow (m : Nat) : ∀ k : Nat, mden v (m ^ k) = mden v m ^ k
  | 0 => by simp [mden_one]
  | k + 1 => by rw [pow_succ, mden_mul, mden_pow m k, pow_succ]

theorem mdenL_prime :
    ∀ (ps : List Nat) (i x : Nat), (∀ q ∈ ps, q.Prime) → ps.Nodup → (hx : x < ps.length) →
      mdenL v ps i ps[x] = v (i + x)
  | [], _, _, _, _, hx => absurd hx (Nat.not_lt_zero _)
  | p :: ps, i, 0, hp, hnd, _ => by
    have hpp : p.Prime := hp p List.mem_cons_self
    simp only [List.getElem_cons_zero, mdenL, hpp.factorization_self, pow_one, Nat.add_zero]
    rw [mdenL_of_fact_zero v p ps (i + 1), mul_one]
    intro q hq
    have hqp : q.Prime := hp q (List.mem_cons_of_mem _ hq)
    have hne : q ≠ p := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hq)
    exact Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp hd))
  | p :: ps, i, x + 1, hp, hnd, hx => by
    have hpp : p.Prime := hp p List.mem_cons_self
    have hx' : x < ps.length := by simpa using hx
    have hmem : ps[x] ∈ ps := List.getElem_mem _
    have hxp : ps[x].Prime := hp _ (List.mem_cons_of_mem _ hmem)
    have hne : p ≠ ps[x] := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hmem)
    simp only [List.getElem_cons_succ, mdenL]
    rw [Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hpp hxp).mp hd)), pow_zero, one_mul,
      mdenL_prime ps (i + 1) x (fun q hq => hp q (List.mem_cons_of_mem _ hq))
        (List.nodup_cons.mp hnd).2 hx']
    congr 1; omega

/-- no `d ∈ [2, k]` with `d * d ≤ p` divides `p` -/
def noSmallDiv (p : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => ((Nat.blt p ((k + 1) * (k + 1)) || !(Nat.beq (p % (k + 1)) 0)) || Nat.blt (k + 1) 2)
      && noSmallDiv p k

theorem noSmallDiv_spec (p : Nat) : ∀ k, noSmallDiv p k = true →
    ∀ d, 2 ≤ d → d ≤ k → d * d ≤ p → ¬ d ∣ p
  | 0, _, d, h2, hk, _ => by omega
  | k + 1, h, d, h2, hk, hdd => by
    simp only [noSmallDiv, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Nat.blt_eq] at h
    rcases Nat.lt_or_ge d (k + 1) with hlt | hge
    · exact noSmallDiv_spec p k h.2 d h2 (by omega) hdd
    · have hd : d = k + 1 := by omega
      subst hd
      rcases h.1 with (h1 | h1) | h1
      · omega
      · exact fun hdvd => by rw [Nat.mod_eq_zero_of_dvd hdvd] at h1; simp at h1
      · omega

theorem prime_of_check (p : Nat) (hp : 2 ≤ p) (hlt : p < 141 * 141)
    (h : noSmallDiv p 140 = true) : p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨hp, fun m hm hle => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hle
  have h140 : m ≤ 140 := by
    by_contra hc
    have : 141 * 141 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    omega
  exact noSmallDiv_spec p 140 h m hm h140 hmm

theorem primes_check : primes.all
    (fun q => (Nat.ble 2 q && Nat.blt q (141 * 141)) && noSmallDiv q 140) = true := by
  decide +kernel

theorem primes_prime : ∀ q ∈ primes, q.Prime := by
  intro q hq
  have h := List.all_eq_true.mp primes_check q hq
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  exact prime_of_check q h.1.1 h.1.2 h.2

theorem primes_chain : primes.IsChain (· < ·) := by decide +kernel

theorem primes_nodup : primes.Nodup :=
  (List.isChain_iff_pairwise.mp primes_chain).imp (fun h => Nat.ne_of_lt h)

theorem primes_length : primes.length = 2048 := rfl

theorem mden_primeOf (x : Nat) (hx : x < 2048) : mden v (primeOf x) = v x := by
  have hx' : x < primes.length := by rw [primes_length]; exact hx
  have h1 : primeOf x = primes[x] := by
    rw [primeOf, primeArr_get x hx]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx']
  have hpr : primes[x].Prime := primes_prime _ (List.getElem_mem _)
  unfold mden
  rw [h1, if_neg hpr.ne_zero, mdenL_prime v primes 0 x primes_prime primes_nodup hx',
    Nat.zero_add]

noncomputable def pden (p : P) : α :=
  P.rec (motive := fun _ => α) 0 (fun c m _ ih => (c : α) * mden v m + ih) p

@[simp] theorem pden_nil : pden v .nil = 0 := rfl
@[simp] theorem pden_cons (c : Int) (m : Nat) (p : P) :
    pden v (.cons c m p) = (c : α) * mden v m + pden v p := rfl

variable {md : Nat} (hmd : ((md : ℕ) : α) = 0)
include hmd

theorem cast_cn (c : Int) : ((cn md c : Int) : α) = (c : α) := by
  have h := Int.emod_add_ediv_mul c (Int.ofNat md)
  have hmd' : ((Int.ofNat md : Int) : α) = 0 := by
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact hmd
  show ((c % (Int.ofNat md) : Int) : α) = _
  conv_rhs => rw [← h]
  push_cast
  rw [hmd']; ring

theorem cast_cn_zero {c : Int} (h : Int.beq' (cn md c) 0 = true) : (c : α) = 0 := by
  have h0 : cn md c = 0 := by
    have := (Int.beq'_eq_beq (cn md c) 0).symm.trans h
    simpa using this
  rw [← cast_cn hmd c, h0]; simp

theorem pden_padd (p q : P) : pden v (padd md p q) = pden v p + pden v q := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons c m p' ih =>
    induction q with
    | nil => simp [padd]
    | cons d n q' ihq =>
      show pden v (Bool.rec
            (Bool.rec (.cons c m (padd md p' (.cons d n q')))
              (.cons d n (padd md (.cons c m p') q')) (Nat.ble m n))
            (Bool.rec (.cons (cn md (Int.add c d)) m (padd md p' q')) (idP (padd md p' q'))
              (Int.beq' (cn md (Int.add c d)) 0))
            (Nat.beq m n)) = _
      cases h1 : Nat.beq m n
      · cases h2 : Nat.ble m n
        · simp only [pden_cons, ih]; ring
        · simp only [pden_cons, ihq]; ring
      · have hmn : m = n := Nat.eq_of_beq_eq_true h1
        subst hmn
        cases h3 : Int.beq' (cn md (Int.add c d)) 0
        · simp only [pden_cons, ih, cast_cn hmd, Int.add_def]; push_cast; ring
        · have h0 := cast_cn_zero hmd h3
          simp only [idP, ih, pden_cons]
          rw [Int.add_def] at h0
          push_cast at h0
          linear_combination (-(mden v m)) * h0

theorem pden_pmulT (c : Int) (m : Nat) (q : P) :
    pden v (pmulT md c m q) = (c : α) * mden v m * pden v q := by
  induction q with
  | nil => simp [pmulT]
  | cons d n q ih =>
    show pden v (Bool.rec (.cons (cn md (Int.mul c d)) (Nat.mul m n) (pmulT md c m q))
      (idP (pmulT md c m q)) (Int.beq' (cn md (Int.mul c d)) 0)) = _
    cases h : Int.beq' (cn md (Int.mul c d)) 0
    · show ((cn md (Int.mul c d) : Int) : α) * mden v (m * n) + pden v (pmulT md c m q) = _
      rw [ih, pden_cons, mden_mul, cast_cn hmd, Int.mul_def]; push_cast; ring
    · have h0 := cast_cn_zero hmd h
      show pden v (idP (pmulT md c m q)) = _
      rw [idP, ih, pden_cons]
      rw [Int.mul_def] at h0; push_cast at h0
      linear_combination (-(mden v m * mden v n)) * h0

theorem pden_pneg (q : P) : pden v (pneg md q) = - pden v q := by
  induction q with
  | nil => simp [pneg]
  | cons d n q ih =>
    show ((cn md (-d) : Int) : α) * mden v n + pden v (pneg md q) = _
    rw [ih, pden_cons, cast_cn hmd]; push_cast; ring

theorem pden_pairUp : ∀ l : List P, ((pairUp md l).map (pden v)).sum = (l.map (pden v)).sum
  | a :: b :: rest => by
    simp only [pairUp, List.map_cons, List.sum_cons, pden_padd v hmd, pden_pairUp rest]; ring
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]

theorem pden_foldr (l : List P) :
    pden v (l.foldr (padd md) .nil) = (l.map (pden v)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, pden_padd v hmd, ih, List.map_cons, List.sum_cons]

theorem pden_sumAll : ∀ (n : Nat) (l : List P),
    pden v (sumAll md n l) = (l.map (pden v)).sum
  | 0, l => by simp only [sumAll, pden_foldr v hmd]
  | _ + 1, [] => by simp [sumAll]
  | _ + 1, [a] => by simp [sumAll]
  | n + 1, a :: b :: l => by
    simp only [sumAll]; rw [pden_sumAll n, pden_pairUp v hmd]

theorem pden_termsOf (q p : P) :
    ((termsOf md q p).map (pden v)).sum = pden v p * pden v q := by
  induction p with
  | nil => simp [termsOf]
  | cons c m p ih =>
    show (pden v (pmulT md c m q) :: (termsOf md q p).map (pden v)).sum = _
    rw [List.sum_cons, ih, pden_pmulT v hmd, pden_cons]; ring

theorem pden_pmul (p q : P) : pden v (pmul md p q) = pden v p * pden v q := by
  unfold pmul
  cases Nat.ble (plen p) (plen q)
  · show pden v (sumAll md 64 (termsOf md p q)) = _
    rw [pden_sumAll v hmd, pden_termsOf v hmd, mul_comm]
  · show pden v (sumAll md 64 (termsOf md q p)) = _
    rw [pden_sumAll v hmd, pden_termsOf v hmd]

theorem pden_ppow (p : P) : ∀ k : Nat, pden v (ppow md p k) = pden v p ^ k
  | 0 => by
    show ((1 : Int) : α) * mden v 1 + 0 = _
    simp [mden_one]
  | k + 1 => by
    show pden v (pmul md (ppow md p k) p) = _
    rw [pden_pmul v hmd, pden_ppow p k, pow_succ]

theorem pden_pconst (k : Int) : pden v (pconst md k) = (k : α) := by
  unfold pconst
  cases h : Int.beq' (cn md k) 0
  · show ((cn md k : Int) : α) * mden v 1 + 0 = _
    simp [mden_one, cast_cn hmd]
  · show (0 : α) = _
    rw [cast_cn_zero hmd h]

omit hmd in
/-- signed value -/
def sv (s : Bool) (x : α) : α := bif s then -x else x

theorem pden_sgn (s : Bool) (p : P) : pden v (sgn md s p) = sv s (pden v p) := by
  cases s
  · rfl
  · show pden v (pneg md p) = _; rw [pden_pneg v hmd]; rfl

omit hmd in
theorem sumL_cons (x : P) (l : List P) :
    ((x :: l).map (pden v)).sum = pden v x + (l.map (pden v)).sum := by simp

omit hmd in
theorem terms_num (k : Int) (s : Bool) (acc : List P) :
    terms md (.num k) s acc = sgn md s (pconst md k) :: acc := rfl
omit hmd in
theorem terms_natCast (k : Nat) (s : Bool) (acc : List P) :
    terms md (.natCast k) s acc = sgn md s (pconst md k) :: acc := rfl
omit hmd in
theorem terms_intCast (k : Int) (s : Bool) (acc : List P) :
    terms md (.intCast k) s acc = sgn md s (pconst md k) :: acc := rfl
omit hmd in
theorem terms_var (x : Nat) (s : Bool) (acc : List P) :
    terms md (.var x) s acc = sgn md s (.cons 1 (primeOf x) .nil) :: acc := rfl
omit hmd in
theorem terms_neg (a : Expr) (s : Bool) (acc : List P) :
    terms md (.neg a) s acc = terms md a (!s) acc := rfl
omit hmd in
theorem terms_add (a b : Expr) (s : Bool) (acc : List P) :
    terms md (.add a b) s acc = terms md a s (terms md b s acc) := rfl
omit hmd in
theorem terms_sub (a b : Expr) (s : Bool) (acc : List P) :
    terms md (.sub a b) s acc = terms md a s (terms md b (!s) acc) := rfl
omit hmd in
theorem terms_mul (a b : Expr) (s : Bool) (acc : List P) :
    terms md (.mul a b) s acc =
      sgn md s (pmul md (sumAll md 64 (terms md a false []))
        (sumAll md 64 (terms md b false []))) :: acc := rfl

omit hmd in
/-- the power term -/
noncomputable def powT (md : Nat) (a : Expr) (k : Nat) : P :=
  Bool.rec
    (Expr.rec (motive := fun _ => P) (fun _ => ppow md (sumAll md 64 (terms md a false [])) k)
      (fun _ => ppow md (sumAll md 64 (terms md a false [])) k)
      (fun _ => ppow md (sumAll md 64 (terms md a false [])) k)
      (fun x => .cons 1 (Nat.pow (primeOf x) k) .nil)
      (fun _ _ => ppow md (sumAll md 64 (terms md a false [])) k)
      (fun _ _ _ _ => ppow md (sumAll md 64 (terms md a false [])) k)
      (fun _ _ _ _ => ppow md (sumAll md 64 (terms md a false [])) k)
      (fun _ _ _ _ => ppow md (sumAll md 64 (terms md a false [])) k)
      (fun _ _ _ => ppow md (sumAll md 64 (terms md a false [])) k) a)
    (.cons 1 1 .nil) (Nat.beq k 0)

omit hmd in
theorem terms_pow (a : Expr) (k : Nat) (s : Bool) (acc : List P) :
    terms md (.pow a k) s acc = sgn md s (powT md a k) :: acc := rfl

theorem terms_sound (ctx : Context α) :
    ∀ e : Expr, VOk 2048 e → ∀ (s : Bool) (acc : List P),
      ((terms md e s acc).map (pden (fun i => ctx.get i))).sum =
        sv s (e.denote ctx) + (acc.map (pden (fun i => ctx.get i))).sum
  | .num k, _, s, acc => by
    rw [terms_num, sumL_cons, pden_sgn _ hmd, pden_pconst _ hmd,
      ← Lean.Grind.CommRing.denoteInt_eq k]; rfl
  | .natCast k, _, s, acc => by
    rw [terms_natCast, sumL_cons, pden_sgn _ hmd, pden_pconst _ hmd]
    have : ((k : Int) : α) = (Expr.natCast k).denote ctx := by
      show ((k : Int) : α) = (k : α); simp
    rw [this]
  | .intCast k, _, s, acc => by
    rw [terms_intCast, sumL_cons, pden_sgn _ hmd, pden_pconst _ hmd]; rfl
  | .var x, h, s, acc => by
    have hx : x < 2048 := h
    rw [terms_var, sumL_cons, pden_sgn _ hmd]
    have : pden (fun i => ctx.get i) (.cons 1 (primeOf x) .nil) = (Expr.var x).denote ctx := by
      show ((1 : Int) : α) * mden _ (primeOf x) + 0 = _
      rw [mden_primeOf _ x hx]; simp; rfl
    rw [this]
  | .neg a, h, s, acc => by
    rw [terms_neg, terms_sound ctx a h]
    have : (Expr.neg a).denote ctx = - a.denote ctx := rfl
    rw [this]; cases s <;> simp [sv]
  | .add a b, h, s, acc => by
    rw [terms_add, terms_sound ctx a h.1, terms_sound ctx b h.2]
    have : (Expr.add a b).denote ctx = a.denote ctx + b.denote ctx := rfl
    rw [this]; cases s <;> simp [sv] <;> ring
  | .sub a b, h, s, acc => by
    rw [terms_sub, terms_sound ctx a h.1, terms_sound ctx b h.2]
    have : (Expr.sub a b).denote ctx = a.denote ctx - b.denote ctx := rfl
    rw [this]; cases s <;> simp [sv] <;> ring
  | .mul a b, h, s, acc => by
    rw [terms_mul, sumL_cons, pden_sgn _ hmd, pden_pmul _ hmd, pden_sumAll _ hmd,
      pden_sumAll _ hmd, terms_sound ctx a h.1, terms_sound ctx b h.2]
    have : (Expr.mul a b).denote ctx = a.denote ctx * b.denote ctx := rfl
    rw [this]; simp [sv]
  | .pow a k, h, s, acc => by
    have ha : VOk 2048 a := h
    have hk : (Expr.pow a k).denote ctx = a.denote ctx ^ k := rfl
    rw [terms_pow, sumL_cons, pden_sgn _ hmd, hk]
    congr 2
    have hgen : pden (fun i => ctx.get i) (ppow md (sumAll md 64 (terms md a false [])) k) =
        a.denote ctx ^ k := by
      rw [pden_ppow _ hmd, pden_sumAll _ hmd, terms_sound ctx a ha]; simp [sv]
    unfold powT
    cases hk0 : Nat.beq k 0
    · cases a with
      | var x =>
        have hx : x < 2048 := ha
        show ((1 : Int) : α) * mden _ (Nat.pow (primeOf x) k) + 0 = _
        rw [Nat.pow_eq, mden_pow, mden_primeOf _ x hx]; simp; rfl
      | num _ => exact hgen
      | natCast _ => exact hgen
      | intCast _ => exact hgen
      | neg _ => exact hgen
      | add _ _ => exact hgen
      | sub _ _ => exact hgen
      | mul _ _ => exact hgen
      | pow _ _ => exact hgen
    · have : k = 0 := Nat.eq_of_beq_eq_true hk0
      subst this
      show ((1 : Int) : α) * mden _ 1 + 0 = _
      simp [mden_one]

theorem norm_sound (ctx : Context α) (e : Expr) (h : VOk 2048 e) :
    pden (fun i => ctx.get i) (norm md e) = e.denote ctx := by
  unfold norm
  rw [pden_sumAll _ hmd, terms_sound hmd ctx e h]; simp [sv]

end Sound

theorem refl_eq {α : Type*} [CommRing α] (md : Nat) (hmd : ((md : ℕ) : α) = 0)
    (ctx : Context α) (a b : Expr)
    (h : check md (.sub a b) = true) : a.denote ctx = b.denote ctx := by
  have h' := Bool.and_eq_true_iff.mp h
  have h2 := norm_sound hmd ctx (.sub a b) ((varsLtA_iff 2048 _ true).mp h'.1).1
  have hnil : norm md (.sub a b) = .nil := by
    have := h'.2
    revert this
    cases norm md (.sub a b) <;> simp [isNil]
  rw [hnil] at h2
  have h3 : a.denote ctx - b.denote ctx = 0 := by
    have : (Expr.sub a b).denote ctx = a.denote ctx - b.denote ctx := rfl
    rw [← this, ← h2]; rfl
  exact sub_eq_zero.mp h3

/-! ### The tactic -/

open Lean Meta Elab Tactic

structure ReifyState where
  atoms : Array Lean.Expr := #[]
  map : Std.HashMap Lean.Expr Nat := {}

abbrev ReifyM := StateT ReifyState MetaM

def mkG (n : Name) : Lean.Expr := mkConst (``Lean.Grind.CommRing.Expr ++ n)

def atomIdx (e : Lean.Expr) : ReifyM Nat := do
  let s ← get
  match s.map[e]? with
  | some i => return i
  | none =>
    for h : j in [0:s.atoms.size] do
      if ← withTransparency .instances <| isDefEq e s.atoms[j] then
        set { s with map := s.map.insert e j }
        return j
    let i := s.atoms.size
    set { s with atoms := s.atoms.push e, map := s.map.insert e i }
    return i

/-- Recognise a closed natural-number literal (raw literal or `OfNat.ofNat ℕ n _`). -/
def natLit? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg! with
      | .lit (.natVal n) => some n
      | _ => none
    else none

partial def reify (e : Lean.Expr) : ReifyM Lean.Expr := do
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then
    return mkApp2 (mkG `add) (← reify e.appFn!.appArg!) (← reify e.appArg!)
  if e.isAppOfArity ``HSub.hSub 6 then
    return mkApp2 (mkG `sub) (← reify e.appFn!.appArg!) (← reify e.appArg!)
  if e.isAppOfArity ``HMul.hMul 6 then
    return mkApp2 (mkG `mul) (← reify e.appFn!.appArg!) (← reify e.appArg!)
  if e.isAppOfArity ``Neg.neg 3 then
    return mkApp (mkG `neg) (← reify e.appArg!)
  if e.isAppOfArity ``HPow.hPow 6 then
    let k := e.appArg!
    let ty := e.getAppArgs[1]!
    if ty.isConstOf ``Nat then
      if let some n := natLit? k then
        return mkApp2 (mkG `pow) (← reify e.appFn!.appArg!) (mkRawNatLit n)
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := natLit? e.appFn!.appArg! then
      return mkApp (mkG `num) (toExpr (Int.ofNat n))
  let i ← atomIdx e
  return mkApp (mkG `var) (mkRawNatLit i)

/-! ### Native pre-check (elaboration time only; mirrors the kernel normaliser) -/

namespace Native
abbrev Q := List (Int × Nat)

def cn (md : Nat) (c : Int) : Int := c % (md : Int)

partial def padd (md : Nat) : Q → Q → Q
  | [], q => q
  | p, [] => p
  | (c, m) :: p', (d, n) :: q' =>
    if m == n then
      let r := padd md p' q'
      let k := cn md (c + d)
      if k == 0 then r else (k, m) :: r
    else if m < n then (d, n) :: padd md ((c, m) :: p') q'
    else (c, m) :: padd md p' ((d, n) :: q')

partial def sumAll (md : Nat) : List Q → Q
  | [] => []
  | [a] => a
  | l =>
    let rec pairUp : List Q → List Q
      | a :: b :: r => padd md a b :: pairUp r
      | l => l
    sumAll md (pairUp l)

def pmul (md : Nat) (p q : Q) : Q :=
  let (p, q) := if p.length ≤ q.length then (p, q) else (q, p)
  sumAll md (p.map fun (c, m) =>
    q.filterMap fun (d, n) => let k := cn md (c * d); if k == 0 then none else some (k, m * n))

def neg (md : Nat) (p : Q) : Q := p.map fun (c, m) => (cn md (-c), m)

def const (md : Nat) (n : Int) : Q := let k := cn md n; if k == 0 then [] else [(k, 1)]

partial def norm (md : Nat) (e : Lean.Expr) : Option Q := do
  match e.getAppFnArgs with
  | (``Lean.Grind.CommRing.Expr.add, #[a, b]) => return padd md (← norm md a) (← norm md b)
  | (``Lean.Grind.CommRing.Expr.sub, #[a, b]) => return padd md (← norm md a) (neg md (← norm md b))
  | (``Lean.Grind.CommRing.Expr.mul, #[a, b]) => return pmul md (← norm md a) (← norm md b)
  | (``Lean.Grind.CommRing.Expr.neg, #[a]) => return neg md (← norm md a)
  | (``Lean.Grind.CommRing.Expr.pow, #[a, k]) =>
    let k ← k.rawNatLit?
    if k == 0 then return [(1, 1)]
    match a.getAppFnArgs with
    | (``Lean.Grind.CommRing.Expr.var, #[x]) => return [(1, (primes.getD (← x.rawNatLit?) 0) ^ k)]
    | _ =>
      let p ← norm md a
      let mut r : Q := [(1, 1)]
      for _ in [0:k] do r := pmul md r p
      return r
  | (``Lean.Grind.CommRing.Expr.var, #[x]) => return [(1, primes.getD (← x.rawNatLit?) 0)]
  | (``Lean.Grind.CommRing.Expr.num, #[k]) => return const md (← k.int?)
  | _ => none

end Native

/-- Prove `A = B` (commutative ring, in which the numeral `md` vanishes; `md = 0` for plain
identities) by reflection; the check is left to the kernel. -/
def reflRing1 (md : Nat) (g : MVarId) : TacticM Unit := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (α, a, b) := t.eq? | throwError "refl_ring1: goal is not an equality"
  let u ← getLevel α
  let some u' := u.dec | throwError "refl_ring1: universe"
  let inst ← synthInstance (mkApp (mkConst ``CommRing [u']) α)
  let ((ea, eb), s) ← (do return (← reify a, ← reify b) : ReifyM _).run {}
  if s.atoms.size > 2048 then throwError "refl_ring1: more than 2048 atoms"
  let atoms := if s.atoms.isEmpty then #[a] else s.atoms
  let ctx ← if h : 0 < atoms.size then (RArray.ofArray atoms h).toExpr α id
    else throwError "refl_ring1: no atoms"
  match Native.norm md (mkApp2 (mkG `sub) ea eb) with
  | none => throwError "refl_ring1: internal error (native normaliser)"
  | some [] => pure ()
  | some r => throwError "refl_ring1: not an identity ({r.length} terms remain)"
  -- the proof of `((md : ℕ) : α) = 0`
  let hmdTy ← mkEq (← mkAppOptM ``Nat.cast #[α, none, mkNatLit md])
    (← mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit 0, none])
  let hmd ← mkFreshExprMVar hmdTy
  let αs ← Term.exprToSyntax α
  let mds := Syntax.mkNumLit (toString md)
  let gs ← Tactic.run hmd.mvarId! do
    evalTactic (← `(tactic| first
      | exact (Nat.cast_zero : ((0 : ℕ) : $αs) = 0)
      | exact CharP.cast_eq_zero $αs $mds
      | (simp only [Nat.cast_ofNat]; assumption)
      | (norm_num; assumption)))
  unless gs.isEmpty do throwError "refl_ring1: could not prove ({md} : _) = 0"
  let pf := mkAppN (mkConst ``refl_eq [u']) #[α, inst, mkNatLit md, ← instantiateMVars hmd,
    ctx, ea, eb, mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)]
  g.assign pf

syntax (name := reflRing1Stx) "refl_ring1" (" (" &"mod" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| refl_ring1) => do reflRing1 0 (← getMainGoal); replaceMainGoal []
  | `(tactic| refl_ring1 (mod := $n)) => do reflRing1 n.getNat (← getMainGoal); replaceMainGoal []

end Work.Reflect
