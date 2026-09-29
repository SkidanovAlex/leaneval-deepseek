import Mathlib
import Submission.Work.Transform.chirpAux
import Submission.Work.Transform.Defs
import Submission.Work.Transform.blendPwWord
import Submission.Work.Transform.blendStretchWord
import Submission.Work.Transform.blendTileWord

/-!
# `Work.Transform.blendWord` — the Kronecker (blend) step of the transform pipeline

`int p :: cvecVal c :: cvecVal u :: R` is turned into `cvecVal w :: int p :: R`, where `w` is the
outer product `w[a * P + b] ~ c[a] * u[b]` (`t = c.length`, `P = u.length`), at cost
`O((t * P) * p ^ 2)`.

`w` is the pointwise product of the *stretched* vector `X = flatten (c.map (replicate P))`
(entry `a * P + b` is `c[a]`) with the *tiled* vector `Y = flatten (replicate t u)` (entry
`a * P + b` is `u[b]`); the two index identities are `chirpAux.getD_map_replicate_flatten` and
`chirpAux.getD_flatten_replicate`.

The three building blocks are proved in the sibling modules:

* `Submission.Work.Transform.blendStretchWord` (`X` from `c`, via `KernelLib.mapList`,
  `LayoutLib.replicate`, `LayoutLib.flatten`);
* `Submission.Work.Transform.blendTileWord` (`Y` from `u`, via `LayoutLib.replicate`,
  `LayoutLib.flatten`);
* `Submission.Work.Transform.blendPwWord` (the pointwise product, via `KernelLib.zipWith`,
  `FxLib.mulS`).

This file only *rearranges* the value stack (with `KernelLib.roll`/`drop` and `LayoutLib.length`)
around these three words and assembles the final statement.  The working stack is a fixed-size
pool, so every `roll` has index `< 5`; the only large values it touches (`ofList X`, `ofList Y`)
have size `O(t * P * p)`, and each is touched `O(1)` times (not once per element).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Transform

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Helpers -/

/-- The coordinate pair of a value, when it is a fixed-point complex number. -/
def pairOf : Val → ℤ × ℤ
  | .cons (.int a) (.int b) => (a, b)
  | _ => (0, 0)

@[simp] theorem pairOf_cfxVal (z : ℤ × ℤ) : pairOf (cfxVal z) = z := rfl

theorem cfxVal_inj {z1 z2 : ℤ × ℤ} (h : cfxVal z1 = cfxVal z2) : z1 = z2 := by
  have h' : z1.1 = z2.1 ∧ z1.2 = z2.2 := by
    simpa [cfxVal, Val.cons.injEq, Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

theorem cfxVal_pairOf_eq {v : Val} (h : ∃ z, v = cfxVal z) : cfxVal (pairOf v) = v := by
  obtain ⟨z, rfl⟩ := h; rfl

theorem map_cfxVal_pairOf (l : List Val)
    (h : ∀ i < l.length, ∃ z, l.getD i .nil = cfxVal z) :
    l.map (fun v => cfxVal (pairOf v)) = l := by
  induction l with
  | nil => simp
  | cons v t ih =>
    have hv : ∃ z, v = cfxVal z := by simpa using h 0 (by simp)
    have ht : ∀ i < t.length, ∃ z, t.getD i .nil = cfxVal z := by
      intro i hi
      simpa using h (i + 1) (by simp; omega)
    rw [List.map_cons, ih ht, cfxVal_pairOf_eq hv]

theorem sum_map_const' {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul]; ring

theorem vsz_ofList_le {S : ℕ} (l : List Val) (h : ∀ i < l.length, vsz (l.getD i .nil) ≤ S) :
    vsz (ofList l) ≤ l.length * S + l.length + 1 := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v t ih =>
    have hv : vsz v ≤ S := by simpa using h 0 (by simp)
    have ht : ∀ i < t.length, vsz (t.getD i .nil) ≤ S := by
      intro i hi
      simpa using h (i + 1) (by simp; omega)
    rw [show ofList (v :: t) = Val.cons v (ofList t) from rfl, chirpAux_vsz_cons]
    have hle := ih ht
    simp only [List.length_cons]
    have expand : (t.length + 1) * S + (t.length + 1) + 1
        = (t.length * S + t.length + 1) + (S + 1) := by ring
    rw [expand]
    omega

/-- Uniform bound on the encoding size of any value met by the blend pipeline. -/
def BW_big (t P p : ℕ) : ℕ := 4 * (t + 1) * (P + 1) * (p + 1)

/-- Uniform per-stage cost bound of the blend pipeline. -/
def BW_bu (t P p : ℕ) : ℕ := (t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1

/-- The stretch invariant: `X` is `c` with every entry repeated `P` times. -/
def StretchI (t P : ℕ) (c : List (ℤ × ℤ)) (X : List Val) : Prop :=
  X.length = t * P ∧ ∀ a < t, ∀ b < P, X.getD (a * P + b) .nil = cfxVal (c.getD a (0, 0))

/-- The tile invariant: `Y` is `u` repeated `t` times. -/
def TileI (t P : ℕ) (u : List (ℤ × ℤ)) (Y : List Val) : Prop :=
  Y.length = t * P ∧ ∀ a < t, ∀ b < P, Y.getD (a * P + b) .nil = cfxVal (u.getD b (0, 0))

theorem vsz_ofList_stretch_le {p t P : ℕ} {c : List (ℤ × ℤ)} {X : List Val}
    (hP : 1 ≤ P) (hclen : c.length = t) (hc : InDiscVec p t c) (hX : StretchI t P c X) :
    vsz (ofList X) ≤ (t + 1) * (P + 1) * (2 * p + 9) := by
  obtain ⟨hlen, hget⟩ := hX
  refine le_trans (vsz_ofList_le (S := 2 * p + 8) X ?_) ?_
  · intro i hi
    have hb : i % P < P := Nat.mod_lt _ (by omega)
    have ha : i / P < t := by
      have h1 : i < t * P := by rw [← hlen]; exact hi
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
    have hii : i / P * P + i % P = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i P
    have hmem : c.getD (i / P) (0, 0) ∈ c := by
      have ha' : i / P < c.length := by rw [hclen]; exact ha
      rw [List.getD_eq_getElem _ _ ha']
      exact List.getElem_mem ha'
    have hXeq : X.getD (i / P * P + i % P) .nil = X.getD i .nil := by rw [hii]
    rw [← hXeq, hget (i / P) ha (i % P) hb]
    exact chirpAux_vsz_cfxVal_le (hc.2 _ hmem)
  · rw [hlen]
    nlinarith [Nat.zero_le t, Nat.zero_le P, Nat.zero_le p]

theorem vsz_ofList_tile_le {p t P : ℕ} {u : List (ℤ × ℤ)} {Y : List Val}
    (hP : 1 ≤ P) (hulen : u.length = P) (hu : InDiscVec p P u) (hY : TileI t P u Y) :
    vsz (ofList Y) ≤ (t + 1) * (P + 1) * (2 * p + 9) := by
  obtain ⟨hlen, hget⟩ := hY
  refine le_trans (vsz_ofList_le (S := 2 * p + 8) Y ?_) ?_
  · intro i hi
    have hb : i % P < P := Nat.mod_lt _ (by omega)
    have ha : i / P < t := by
      have h1 : i < t * P := by rw [← hlen]; exact hi
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
    have hii : i / P * P + i % P = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i P
    have hmem : u.getD (i % P) (0, 0) ∈ u := by
      have hb' : i % P < u.length := by rw [hulen]; exact hb
      rw [List.getD_eq_getElem _ _ hb']
      exact List.getElem_mem hb'
    have hYeq : Y.getD (i / P * P + i % P) .nil = Y.getD i .nil := by rw [hii]
    rw [← hYeq, hget (i / P) ha (i % P) hb]
    exact chirpAux_vsz_cfxVal_le (hu.2 _ hmem)
  · rw [hlen]
    nlinarith [Nat.zero_le t, Nat.zero_le P, Nat.zero_le p]

theorem sum_take_map_le {A : List Val} {BIG k : ℕ} (h : ∀ v ∈ A.take (k+1), vsz v ≤ BIG) :
    ((A.take (k+1)).map vsz).sum ≤ (k+1) * BIG := by
  have h1 : ((A.take (k+1)).map vsz).sum ≤ ((A.take (k+1)).map (fun _ => BIG)).sum :=
    List.sum_le_sum (fun v hv => h v hv)
  rw [sum_map_const'] at h1
  exact le_trans h1 (Nat.mul_le_mul_right _ (List.length_take_le _ _))

theorem wconseq {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hP' s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hP') s R hR
  exact ⟨out, s', n, hQ vs out hP' hQh, he, le_trans hn (hC vs hP'), hstk, hoth⟩

theorem wseq {main : Cmd} {p q : Cmd} {A : List Val} {Q1 Q2 : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => Q1 out) (fun _ => c1))
    (h2 : WordR main q Q1 (fun _ out => Q2 out) (fun _ => c2)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => Q2 out) (fun _ => c1 + c2) := by
  intro vs hvs s Rg hRg
  rw [hvs] at hRg
  obtain ⟨mid, s2, n1, hQ1, he1, hn1, hstk1, hoth1⟩ := h1 A rfl s Rg hRg
  obtain ⟨out, s3, n2, hQ2, he2, hn2, hstk2, hoth2⟩ := h2 mid hQ1 s2 Rg hstk1
  exact ⟨out, s3, n1 + n2, hQ2, Eval.seq he1 he2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem rollCost_le {Kr k BIG BU : ℕ} (hk : k + 1 ≤ 5) (hBIG : BIG ≤ 4 * BU) (hBIG1 : 1 ≤ BIG)
    {s : ℕ} (hs : s ≤ (k + 1) * BIG) : Kr * (k + 1) * (s + 1) ≤ 200 * Kr * BU := by
  have h2 : (k + 1) * BIG ≤ 5 * BIG := Nat.mul_le_mul_right BIG hk
  have hs6 : s + 1 ≤ 6 * BIG := by omega
  have h1 : Kr * (k + 1) ≤ Kr * 5 := Nat.mul_le_mul_left Kr hk
  calc Kr * (k + 1) * (s + 1) ≤ (Kr * 5) * (6 * BIG) := Nat.mul_le_mul h1 hs6
    _ = 30 * (Kr * BIG) := by ring
    _ ≤ 30 * (Kr * (4 * BU)) := Nat.mul_le_mul_left 30 (Nat.mul_le_mul_left Kr hBIG)
    _ ≤ 200 * (Kr * BU) := by nlinarith [Nat.zero_le Kr, Nat.zero_le BU]
    _ = 200 * Kr * BU := by ring

theorem sizeCost_le {K c BU : ℕ} (hc : c ≤ 4 * BU) (hBU1 : 1 ≤ BU) : K * (c + 1) ≤ 5 * K * BU := by
  have h1 : c + 1 ≤ 5 * BU := by omega
  calc K * (c + 1) ≤ K * (5 * BU) := Nat.mul_le_mul_left K h1
    _ = 5 * K * BU := by ring

/-- `1 ≤ a * b` from `1 ≤ a`, `1 ≤ b`. -/
theorem one_le_mul' {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  simpa using Nat.mul_le_mul ha hb

/-- `n + 1 ≤ (n + 1) ^ 2`. -/
theorem le_sq_succ (n : ℕ) : n + 1 ≤ (n + 1) ^ 2 := by
  have h : (n + 1) * 1 ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_left (n + 1) (by omega)
  simpa [pow_two] using h

/-! ## Temporary copies of the three delegated words (replaced by imports later) -/




/-- Uniform per-stage cost of the blend pipeline. -/
def BW_c (Kroll Klen Kdrop Kst Ktl Kpw : ℕ) : ℕ :=
  200 * Kroll + 5 * Klen + 5 * Kdrop + Kst + Ktl + 2 * Kpw

/-- The postcondition of the blend pipeline after the pointwise product. -/
def FinalPost (p t P : ℕ) (c u : List (ℤ × ℤ)) (R : List Val) (out : List Val) : Prop :=
  ∃ X Y zs : List Val, out = ofList zs :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y ∧
    zs.length = X.length ∧
    ∀ i < X.length, ∃ z1 z2 w : ℤ × ℤ, X.getD i Val.nil = cfxVal z1 ∧ Y.getD i Val.nil = cfxVal z2 ∧
      zs.getD i Val.nil = cfxVal w ∧ inDisc p w ∧
      (2 : ℝ) ^ p * ‖fxC p w - fxC p z1 * fxC p z2‖ < 2

theorem blendWord : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p t P : ℕ) (c u : List (ℤ × ℤ)) (R : List HvdH.Val),
      100 ≤ p → 1 ≤ t → 1 ≤ P → c.length = t → u.length = P →
      HvdH.InDiscVec p t c → HvdH.InDiscVec p P u →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.cvecVal c :: HvdH.cvecVal u :: R)
        (fun vs out => vs = HvdH.Val.int p :: HvdH.cvecVal c :: HvdH.cvecVal u :: R ∧
          ∃ (w : List (ℤ × ℤ)),
            out = HvdH.cvecVal w :: HvdH.Val.int p :: R ∧
            w.length = t * P ∧ HvdH.InDiscVec p (t * P) w ∧
            ∀ a < t, ∀ b < P, (2 : ℝ) ^ p * ‖HvdH.fxC p (w.getD (a * P + b) (0, 0)) -
              HvdH.fxC p (c.getD a (0, 0)) * HvdH.fxC p (u.getD b (0, 0))‖ < 2)
        (fun _ => K * ((t * P) * p ^ 2) + K) := by
  intro hK hI hL hF
  obtain ⟨pwProg, Kpw, hpw⟩ := blendPwWord hK hF
  obtain ⟨stProg, Kst, hst⟩ := blendStretchWord hK hL
  obtain ⟨tlProg, Ktl, htl⟩ := blendTileWord hK hL
  obtain ⟨rollP, Kroll, hroll⟩ := hK.roll
  obtain ⟨lenP, Klen, hlen⟩ := hL.length
  obtain ⟨dropP, Kdrop, hdrop⟩ := hK.drop
  refine ⟨
       (((((((((((((((rollP 2 ;;; lenP) ;;; rollP 3) ;;; lenP) ;;; rollP 4) ;;; rollP 3) ;;; rollP 3)
              ;;; stProg) ;;; rollP 3) ;;; rollP 4) ;;; rollP 1) ;;; tlProg) ;;; rollP 2) ;;; dropP)
              ;;; rollP 1) ;;; pwProg),
     200 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1), ?_⟩
  intro main p t P c u R hp ht hP hclen hulen hdc hdu
  have hrollCost : 200 * Kroll * BW_bu t P p ≤ BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p := by
    simp only [BW_c]; exact Nat.mul_le_mul_right _ (by omega)
  have hlenCost : 5 * Klen * BW_bu t P p ≤ BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p := by
    simp only [BW_c]; exact Nat.mul_le_mul_right _ (by omega)
  have hdropCost : 5 * Kdrop * BW_bu t P p ≤ BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p := by
    simp only [BW_c]; exact Nat.mul_le_mul_right _ (by omega)
  have hstCost : Kst * BW_bu t P p ≤ BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p := by
    simp only [BW_c]; exact Nat.mul_le_mul_right _ (by omega)
  have htlCost : Ktl * BW_bu t P p ≤ BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p := by
    simp only [BW_c]; exact Nat.mul_le_mul_right _ (by omega)
  have hpwCost : 2 * Kpw * BW_bu t P p ≤ BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p := by
    simp only [BW_c]; exact Nat.mul_le_mul_right _ (by omega)
  have hBU1 : 1 ≤ BW_bu t P p := by
    simp only [BW_bu]
    have h1 : 1 ≤ t + 1 := by omega
    have h2 : 1 ≤ (P + 1) * (p + 1) ^ 2 + 1 := by
      have hp2 : (0:ℕ) < (P + 1) * (p + 1) ^ 2 := by positivity
      omega
    exact le_trans (one_le_mul' h1 h2) (Nat.le_add_right _ 1)
  have hBIG1 : 1 ≤ BW_big t P p := by
    simp only [BW_big]
    exact one_le_mul' (one_le_mul' (one_le_mul' (show (1:ℕ) ≤ 4 by norm_num) (by omega))
      (by omega)) (by omega)
  have hBU : BW_big t P p ≤ 4 * BW_bu t P p := by
    simp only [BW_big, BW_bu]
    have hA : (P + 1) * (p + 1) ≤ (P + 1) * (p + 1) ^ 2 :=
      Nat.mul_le_mul_left (P + 1) (le_sq_succ p)
    have hB : (P + 1) * (p + 1) ^ 2 ≤ (P + 1) * (p + 1) ^ 2 + 1 :=
      Nat.le_add_right _ 1
    have hC : (P + 1) * (p + 1) ≤ (P + 1) * (p + 1) ^ 2 + 1 := le_trans hA hB
    have hD : (t + 1) * ((P + 1) * (p + 1)) ≤ (t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) :=
      Nat.mul_le_mul_left (t + 1) hC
    have hF : (t + 1) * ((P + 1) * (p + 1)) ≤ (t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1 :=
      le_trans hD (Nat.le_add_right _ 1)
    have hG : 4 * ((t + 1) * ((P + 1) * (p + 1))) ≤
        4 * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1) :=
      Nat.mul_le_mul_left 4 hF
    calc 4 * (t + 1) * (P + 1) * (p + 1) = 4 * ((t + 1) * ((P + 1) * (p + 1))) := by ring
      _ ≤ 4 * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1) := hG
  have hS1 : vsz (cvecVal c) ≤ BW_big t P p := by
    have h := chirpAux_vsz_cvecVal_le hdc
    simp only [BW_big]
    have h1 : t * (2 * p + 8) + t + 1 ≤ (t + 1) * (2 * p + 9) := by
      have e : (t + 1) * (2 * p + 9) = t * (2 * p + 9) + (2 * p + 9) := by ring
      have e2 : t * (2 * p + 9) = t * (2 * p + 8) + t := by ring
      rw [e, e2]; omega
    have h2 : (t + 1) * (2 * p + 9) ≤ (t + 1) * (4 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
    have h3 : 4 * (t + 1) * (p + 1) ≤ 4 * (t + 1) * (P + 1) * (p + 1) := by
      have hm : (p + 1) ≤ (P + 1) * (p + 1) := Nat.le_mul_of_pos_left (p + 1) (by omega)
      calc 4 * (t + 1) * (p + 1) = 4 * (t + 1) * (p + 1) := rfl
        _ ≤ 4 * (t + 1) * ((P + 1) * (p + 1)) := Nat.mul_le_mul_left _ hm
        _ = 4 * (t + 1) * (P + 1) * (p + 1) := by ring
    calc vsz (cvecVal c) ≤ t * (2 * p + 8) + t + 1 := h
      _ ≤ (t + 1) * (2 * p + 9) := h1
      _ ≤ (t + 1) * (4 * (p + 1)) := h2
      _ = 4 * (t + 1) * (p + 1) := by ring
      _ ≤ 4 * (t + 1) * (P + 1) * (p + 1) := h3
  have hS2 : vsz (cvecVal u) ≤ BW_big t P p := by
    have h := chirpAux_vsz_cvecVal_le hdu
    simp only [BW_big]
    have h1 : P * (2 * p + 8) + P + 1 ≤ (P + 1) * (2 * p + 9) := by
      have e : (P + 1) * (2 * p + 9) = P * (2 * p + 9) + (2 * p + 9) := by ring
      have e2 : P * (2 * p + 9) = P * (2 * p + 8) + P := by ring
      rw [e, e2]; omega
    have h2 : (P + 1) * (2 * p + 9) ≤ (P + 1) * (4 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
    have h3 : 4 * (P + 1) * (p + 1) ≤ 4 * (t + 1) * (P + 1) * (p + 1) := by
      have hm : (P + 1) * (p + 1) ≤ (t + 1) * ((P + 1) * (p + 1)) :=
        Nat.le_mul_of_pos_left ((P + 1) * (p + 1)) (by omega)
      calc 4 * (P + 1) * (p + 1) = 4 * ((P + 1) * (p + 1)) := by ring
        _ ≤ 4 * ((t + 1) * ((P + 1) * (p + 1))) := Nat.mul_le_mul_left 4 hm
        _ = 4 * (t + 1) * (P + 1) * (p + 1) := by ring
    calc vsz (cvecVal u) ≤ P * (2 * p + 8) + P + 1 := h
      _ ≤ (P + 1) * (2 * p + 9) := h1
      _ ≤ (P + 1) * (4 * (p + 1)) := h2
      _ = 4 * (P + 1) * (p + 1) := by ring
      _ ≤ 4 * (t + 1) * (P + 1) * (p + 1) := h3
  have hPv : vsz (Val.int P) ≤ BW_big t P p := by
    have h : vsz (Val.int (P : ℤ)) ≤ P + 2 := by
      rw [chirpAux_vsz_int]; simp only [isz, Int.natAbs_natCast]
      have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := P)); omega
    simp only [BW_big]
    have h1 : 4 * (P + 1) ≤ 4 * (t + 1) * (P + 1) := by
      have hm : (P + 1) ≤ (t + 1) * (P + 1) := Nat.le_mul_of_pos_left (P + 1) (by omega)
      calc 4 * (P + 1) = 4 * (P + 1) := rfl
        _ ≤ 4 * ((t + 1) * (P + 1)) := Nat.mul_le_mul_left 4 hm
        _ = 4 * (t + 1) * (P + 1) := by ring
    have h2 : 4 * (t + 1) * (P + 1) ≤ 4 * (t + 1) * (P + 1) * (p + 1) := by
      have hm : (P + 1) ≤ (P + 1) * (p + 1) := Nat.le_mul_of_pos_right (P + 1) (by omega)
      calc 4 * (t + 1) * (P + 1) = 4 * (t + 1) * (P + 1) := rfl
        _ ≤ 4 * (t + 1) * ((P + 1) * (p + 1)) := Nat.mul_le_mul_left _ hm
        _ = 4 * (t + 1) * (P + 1) * (p + 1) := by ring
    calc vsz (Val.int P) ≤ P + 2 := h
      _ ≤ 4 * (P + 1) := by omega
      _ ≤ 4 * (t + 1) * (P + 1) := h1
      _ ≤ 4 * (t + 1) * (P + 1) * (p + 1) := h2
  have hpv : vsz (Val.int p) ≤ BW_big t P p := by
    have h : vsz (Val.int (p : ℤ)) ≤ p + 2 := by
      rw [chirpAux_vsz_int]; simp only [isz, Int.natAbs_natCast]
      have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p)); omega
    simp only [BW_big]
    calc vsz (Val.int p) ≤ p + 2 := h
      _ ≤ 4 * (p + 1) := by omega
      _ ≤ 4 * (t + 1) * (p + 1) := by
          have hm : (p + 1) ≤ (t + 1) * (p + 1) := Nat.le_mul_of_pos_left (p + 1) (by omega)
          calc 4 * (p + 1) = 4 * (p + 1) := rfl
            _ ≤ 4 * ((t + 1) * (p + 1)) := Nat.mul_le_mul_left 4 hm
            _ = 4 * (t + 1) * (p + 1) := by ring
      _ ≤ 4 * (t + 1) * (P + 1) * (p + 1) := by
          have hm : (p + 1) ≤ (P + 1) * (p + 1) := Nat.le_mul_of_pos_left (p + 1) (by omega)
          calc 4 * (t + 1) * (p + 1) = 4 * (t + 1) * (p + 1) := rfl
            _ ≤ 4 * (t + 1) * ((P + 1) * (p + 1)) := Nat.mul_le_mul_left _ hm
            _ = 4 * (t + 1) * (P + 1) * (p + 1) := by ring
  have hTv : vsz (Val.int t) ≤ BW_big t P p := by
    have h : vsz (Val.int (t : ℤ)) ≤ t + 2 := by
      rw [chirpAux_vsz_int]; simp only [isz, Int.natAbs_natCast]
      have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := t)); omega
    simp only [BW_big]
    have h1 : 4 * (t + 1) * (P + 1) ≤ 4 * (t + 1) * (P + 1) * (p + 1) := by
      have hm : (P + 1) ≤ (P + 1) * (p + 1) := Nat.le_mul_of_pos_right (P + 1) (by omega)
      calc 4 * (t + 1) * (P + 1) = 4 * (t + 1) * (P + 1) := rfl
        _ ≤ 4 * (t + 1) * ((P + 1) * (p + 1)) := Nat.mul_le_mul_left _ hm
        _ = 4 * (t + 1) * (P + 1) * (p + 1) := by ring
    calc vsz (Val.int t) ≤ t + 2 := h
      _ ≤ 4 * (t + 1) := by omega
      _ ≤ 4 * (t + 1) * (P + 1) := by
          have hm : (t + 1) ≤ (P + 1) * (t + 1) := Nat.le_mul_of_pos_left (t + 1) (by omega)
          calc 4 * (t + 1) = 4 * (t + 1) := rfl
            _ ≤ 4 * ((P + 1) * (t + 1)) := Nat.mul_le_mul_left 4 hm
            _ = 4 * (t + 1) * (P + 1) := by ring
      _ ≤ 4 * (t + 1) * (P + 1) * (p + 1) := h1
  have hSX_of : ∀ {X : List Val}, StretchI t P c X → vsz (ofList X) ≤ BW_big t P p := by
    intro X hX
    have h := vsz_ofList_stretch_le hP hclen hdc hX
    simp only [BW_big]
    calc vsz (ofList X) ≤ (t + 1) * (P + 1) * (2 * p + 9) := h
      _ ≤ (t + 1) * (P + 1) * (4 * (p + 1)) :=
          Nat.mul_le_mul_left ((t + 1) * (P + 1)) (by omega)
      _ = 4 * (t + 1) * (P + 1) * (p + 1) := by ring
  have hSY_of : ∀ {Y : List Val}, TileI t P u Y → vsz (ofList Y) ≤ BW_big t P p := by
    intro Y hY
    have h := vsz_ofList_tile_le hP hulen hdu hY
    simp only [BW_big]
    calc vsz (ofList Y) ≤ (t + 1) * (P + 1) * (2 * p + 9) := h
      _ ≤ (t + 1) * (P + 1) * (4 * (p + 1)) :=
          Nat.mul_le_mul_left ((t + 1) * (P + 1)) (by omega)
      _ = 4 * (t + 1) * (P + 1) * (p + 1) := by ring
  have s1 : WordR main (rollP 2)
      (fun vs => vs = Val.int p :: cvecVal c :: cvecVal u :: R)
      (fun _ out => out = cvecVal u :: Val.int p :: cvecVal c :: R)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 2) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout; rw [hvs] at hout; rw [hout]; simp
    · intro vs hvs
      rw [hvs]
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 2) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl
      exacts [hpv, hS1, hS2]
  have s2 : WordR main lenP
      (fun vs => vs = cvecVal u :: Val.int p :: cvecVal c :: R)
      (fun _ out => out = Val.int P :: cvecVal u :: Val.int p :: cvecVal c :: R)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    intro vs hvs s Rg hRg
    rw [hvs] at hRg
    obtain ⟨out, s', n, hpost, he, hn, hstk, hoth⟩ :=
      hlen main (u.map cfxVal) (cvecVal u :: Val.int p :: cvecVal c :: R)
        ⟨Val.int p :: cvecVal c :: R, rfl⟩ s Rg hRg
    obtain ⟨rest, hvs', hout'⟩ := hpost
    have h3 : rest = Val.int p :: cvecVal c :: R := by
      have h1 : cvecVal u = ofList (u.map cfxVal) := rfl
      rw [h1] at hvs'
      simpa using hvs'.symm
    have h2 : (u.map cfxVal).length = P := by simp [List.length_map, hulen]
    refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
    · rw [hout', h2, h3]; rfl
    · refine le_trans hn (le_trans ?_ hlenCost)
      calc Klen * (vsz (ofList (u.map cfxVal)) + 1) = Klen * (vsz (cvecVal u) + 1) := rfl
        _ ≤ Klen * (BW_big t P p + 1) := Nat.mul_le_mul_left Klen (Nat.add_le_add_right hS2 1)
        _ ≤ 5 * Klen * BW_bu t P p := sizeCost_le (K := Klen) (c := BW_big t P p) hBU hBU1
  have s3 : WordR main (rollP 3)
      (fun vs => vs = Val.int P :: cvecVal u :: Val.int p :: cvecVal c :: R)
      (fun _ out => out = cvecVal c :: Val.int P :: cvecVal u :: Val.int p :: R)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 3) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout; rw [hvs] at hout; rw [hout]; simp
    · intro vs hvs
      rw [hvs]
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 3) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hPv, hS2, hpv, hS1]
  have s4 : WordR main lenP
      (fun vs => vs = cvecVal c :: Val.int P :: cvecVal u :: Val.int p :: R)
      (fun _ out => out = Val.int t :: cvecVal c :: Val.int P :: cvecVal u :: Val.int p :: R)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    intro vs hvs s Rg hRg
    rw [hvs] at hRg
    obtain ⟨out, s', n, hpost, he, hn, hstk, hoth⟩ :=
      hlen main (c.map cfxVal) (cvecVal c :: Val.int P :: cvecVal u :: Val.int p :: R)
        ⟨Val.int P :: cvecVal u :: Val.int p :: R, rfl⟩ s Rg hRg
    obtain ⟨rest, hvs', hout'⟩ := hpost
    have h3 : rest = Val.int P :: cvecVal u :: Val.int p :: R := by
      have h1 : cvecVal c = ofList (c.map cfxVal) := rfl
      rw [h1] at hvs'
      simpa using hvs'.symm
    have h2 : (c.map cfxVal).length = t := by simp [List.length_map, hclen]
    refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
    · rw [hout', h2, h3]; rfl
    · refine le_trans hn (le_trans ?_ hlenCost)
      calc Klen * (vsz (ofList (c.map cfxVal)) + 1) = Klen * (vsz (cvecVal c) + 1) := rfl
        _ ≤ Klen * (BW_big t P p + 1) := Nat.mul_le_mul_left Klen (Nat.add_le_add_right hS1 1)
        _ ≤ 5 * Klen * BW_bu t P p := sizeCost_le (K := Klen) (c := BW_big t P p) hBU hBU1
  have s5 : WordR main (rollP 4)
      (fun vs => vs = Val.int t :: cvecVal c :: Val.int P :: cvecVal u :: Val.int p :: R)
      (fun _ out => out = Val.int p :: Val.int t :: cvecVal c :: Val.int P :: cvecVal u :: R)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 4) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout; rw [hvs] at hout; rw [hout]; simp
    · intro vs hvs
      rw [hvs]
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 4) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      exacts [hTv, hS1, hPv, hS2, hpv]
  have s6 : WordR main (rollP 3)
      (fun vs => vs = Val.int p :: Val.int t :: cvecVal c :: Val.int P :: cvecVal u :: R)
      (fun _ out => out = Val.int P :: Val.int p :: Val.int t :: cvecVal c :: cvecVal u :: R)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 3) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout; rw [hvs] at hout; rw [hout]; simp
    · intro vs hvs
      rw [hvs]
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 3) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hpv, hTv, hS1, hPv]
  have s7 : WordR main (rollP 3)
      (fun vs => vs = Val.int P :: Val.int p :: Val.int t :: cvecVal c :: cvecVal u :: R)
      (fun _ out => out = cvecVal c :: Val.int P :: Val.int p :: Val.int t :: cvecVal u :: R)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 3) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout; rw [hvs] at hout; rw [hout]; simp
    · intro vs hvs
      rw [hvs]
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 3) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hPv, hpv, hTv, hS1]
  have s8 : WordR main stProg
      (fun vs => vs = cvecVal c :: Val.int P :: Val.int p :: Val.int t :: cvecVal u :: R)
      (fun _ out => ∃ X : List Val,
        out = ofList X :: Val.int P :: Val.int p :: Val.int t :: cvecVal u :: R ∧
        StretchI t P c X)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hst main p t P c (cvecVal u :: R) hclen hdc) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]
    · intro vs out hvs hout
      obtain ⟨X, hout', hlen', hget⟩ := hout
      exact ⟨X, hout', ⟨hlen', hget⟩⟩
    · intro vs _
      exact le_trans (le_of_eq (by simp [BW_bu])) hstCost
  have s9 : WordR main (rollP 3)
      (fun vs => ∃ X : List Val,
        vs = ofList X :: Val.int P :: Val.int p :: Val.int t :: cvecVal u :: R ∧ StretchI t P c X)
      (fun _ out => ∃ X : List Val,
        out = Val.int t :: ofList X :: Val.int P :: Val.int p :: cvecVal u :: R ∧ StretchI t P c X)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 3) ?_ ?_ ?_
    · intro vs hvs; obtain ⟨X, rfl, hX⟩ := hvs; simp
    · intro vs out hvs hout
      obtain ⟨X, rfl, hX⟩ := hvs
      rw [hout]
      exact ⟨X, by simp, hX⟩
    · intro vs hvs
      obtain ⟨X, rfl, hX⟩ := hvs
      have hSX : vsz (ofList X) ≤ BW_big t P p := hSX_of hX
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 3) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hSX, hPv, hpv, hTv]
  have s10 : WordR main (rollP 4)
      (fun vs => ∃ X : List Val,
        vs = Val.int t :: ofList X :: Val.int P :: Val.int p :: cvecVal u :: R ∧ StretchI t P c X)
      (fun _ out => ∃ X : List Val,
        out = cvecVal u :: Val.int t :: ofList X :: Val.int P :: Val.int p :: R ∧ StretchI t P c X)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 4) ?_ ?_ ?_
    · intro vs hvs; obtain ⟨X, rfl, hX⟩ := hvs; simp
    · intro vs out hvs hout
      obtain ⟨X, rfl, hX⟩ := hvs
      rw [hout]
      exact ⟨X, by simp, hX⟩
    · intro vs hvs
      obtain ⟨X, rfl, hX⟩ := hvs
      have hSX : vsz (ofList X) ≤ BW_big t P p := hSX_of hX
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 4) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      exacts [hTv, hSX, hPv, hpv, hS2]
  have s11 : WordR main (rollP 1)
      (fun vs => ∃ X : List Val,
        vs = cvecVal u :: Val.int t :: ofList X :: Val.int P :: Val.int p :: R ∧ StretchI t P c X)
      (fun _ out => ∃ X : List Val,
        out = Val.int t :: cvecVal u :: ofList X :: Val.int P :: Val.int p :: R ∧ StretchI t P c X)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 1) ?_ ?_ ?_
    · intro vs hvs; obtain ⟨X, rfl, hX⟩ := hvs; simp
    · intro vs out hvs hout
      obtain ⟨X, rfl, hX⟩ := hvs
      rw [hout]
      exact ⟨X, by simp, hX⟩
    · intro vs hvs
      obtain ⟨X, rfl, hX⟩ := hvs
      have hSX : vsz (ofList X) ≤ BW_big t P p := hSX_of hX
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 1) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl
      exacts [hS2, hTv]
  have s12 : WordR main tlProg
      (fun vs => ∃ X : List Val,
        vs = Val.int t :: cvecVal u :: ofList X :: Val.int P :: Val.int p :: R ∧ StretchI t P c X)
      (fun _ out => ∃ X Y : List Val,
        out = ofList Y :: ofList X :: Val.int P :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    intro vs hvs s Rg hRg
    obtain ⟨X, rfl, hX⟩ := hvs
    obtain ⟨out, s', n, hpost, he, hn, hstk, hoth⟩ :=
      htl main p t P u (ofList X :: Val.int P :: Val.int p :: R) hulen hdu
        (Val.int t :: cvecVal u :: ofList X :: Val.int P :: Val.int p :: R) rfl s Rg hRg
    obtain ⟨Y, hout, hlen', hget⟩ := hpost
    refine ⟨out, s', n, ⟨X, Y, hout, hX, ⟨hlen', hget⟩⟩, he, ?_, hstk, hoth⟩
    refine le_trans hn (le_trans ?_ htlCost)
    have h1 : (t + 1) * ((P + 1) * (p + 1) + 1) + 1 ≤ BW_bu t P p := by
      simp only [BW_bu]
      have h2 : (P + 1) * (p + 1) + 1 ≤ (P + 1) * (p + 1) ^ 2 + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (P + 1) (le_sq_succ p)) 1
      exact Nat.add_le_add_right (Nat.mul_le_mul_left (t + 1) h2) 1
    exact Nat.mul_le_mul_left Ktl h1
  have s13 : WordR main (rollP 2)
      (fun vs => ∃ X Y : List Val,
        vs = ofList Y :: ofList X :: Val.int P :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ out => ∃ X Y : List Val,
        out = Val.int P :: ofList Y :: ofList X :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 2) ?_ ?_ ?_
    · intro vs hvs; obtain ⟨X, Y, rfl, hX, hY⟩ := hvs; simp
    · intro vs out hvs hout
      obtain ⟨X, Y, rfl, hX, hY⟩ := hvs
      rw [hout]
      exact ⟨X, Y, by simp, hX, hY⟩
    · intro vs hvs
      obtain ⟨X, Y, rfl, hX, hY⟩ := hvs
      have hSX : vsz (ofList X) ≤ BW_big t P p := hSX_of hX
      have hSY : vsz (ofList Y) ≤ BW_big t P p := hSY_of hY
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 2) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl | rfl
      exacts [hSY, hSX, hPv]
  have s14 : WordR main dropP
      (fun vs => ∃ X Y : List Val,
        vs = Val.int P :: ofList Y :: ofList X :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ out => ∃ X Y : List Val,
        out = ofList Y :: ofList X :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hdrop main) ?_ ?_ ?_
    · intro vs hvs; obtain ⟨X, Y, rfl, hX, hY⟩ := hvs; simp
    · intro vs out hvs hout
      obtain ⟨X, Y, rfl, hX, hY⟩ := hvs
      obtain ⟨v, rest, hveq, hrest⟩ := hout
      rw [hrest]
      have h3 : rest = ofList Y :: ofList X :: Val.int p :: R :=
        (List.cons.inj hveq.symm).2
      rw [h3]
      exact ⟨X, Y, rfl, hX, hY⟩
    · intro vs hvs
      obtain ⟨X, Y, rfl, hX, hY⟩ := hvs
      have hhead : (Val.int P :: ofList Y :: ofList X :: Val.int p :: R).headD Val.nil
          = Val.int P := rfl
      rw [hhead]
      refine le_trans (le_trans ?_ (sizeCost_le (K := Kdrop) (c := BW_big t P p) hBU hBU1)) hdropCost
      exact Nat.mul_le_mul_left Kdrop (Nat.add_le_add_right hPv 1)
  have s15 : WordR main (rollP 1)
      (fun vs => ∃ X Y : List Val,
        vs = ofList Y :: ofList X :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ out => ∃ X Y : List Val,
        out = ofList X :: ofList Y :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    refine wconseq (hroll main 1) ?_ ?_ ?_
    · intro vs hvs; obtain ⟨X, Y, rfl, hX, hY⟩ := hvs; simp
    · intro vs out hvs hout
      obtain ⟨X, Y, rfl, hX, hY⟩ := hvs
      rw [hout]
      exact ⟨X, Y, by simp, hX, hY⟩
    · intro vs hvs
      obtain ⟨X, Y, rfl, hX, hY⟩ := hvs
      have hSX : vsz (ofList X) ≤ BW_big t P p := hSX_of hX
      have hSY : vsz (ofList Y) ≤ BW_big t P p := hSY_of hY
      refine le_trans (rollCost_le (Kr := Kroll) (BIG := BW_big t P p) (BU := BW_bu t P p)
        (k := 1) (by norm_num) hBU hBIG1 ?_) hrollCost
      apply sum_take_map_le
      intro v hv
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl
      exacts [hSY, hSX]
  have s16 : WordR main pwProg
      (fun vs => ∃ X Y : List Val,
        vs = ofList X :: ofList Y :: Val.int p :: R ∧ StretchI t P c X ∧ TileI t P u Y)
      (fun _ out => FinalPost p t P c u R out)
      (fun _ => BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p) := by
    intro vs hvs s Rg hRg
    obtain ⟨X, Y, rfl, hX, hY⟩ := hvs
    have hXlen : X.length = t * P := hX.1
    have hYlen : Y.length = t * P := hY.1
    have hlen' : X.length = Y.length := by rw [hXlen, hYlen]
    have hdisc : ∀ i < X.length, ∃ z1 z2 : ℤ × ℤ, X.getD i Val.nil = cfxVal z1 ∧
        Y.getD i Val.nil = cfxVal z2 ∧ inDisc p z1 ∧ inDisc p z2 := by
      intro i hi
      have hii : i / P * P + i % P = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i P
      have hb : i % P < P := Nat.mod_lt _ (by omega)
      have ha : i / P < t := by
        have h1 : i < t * P := by rw [← hXlen]; exact hi
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
      have hmemc : c.getD (i / P) (0, 0) ∈ c := by
        have ha' : i / P < c.length := by rw [hclen]; exact ha
        rw [List.getD_eq_getElem _ _ ha']; exact List.getElem_mem ha'
      have hmemu : u.getD (i % P) (0, 0) ∈ u := by
        have hb' : i % P < u.length := by rw [hulen]; exact hb
        rw [List.getD_eq_getElem _ _ hb']; exact List.getElem_mem hb'
      have hXeq : X.getD (i / P * P + i % P) Val.nil = X.getD i Val.nil := by rw [hii]
      have hYeq : Y.getD (i / P * P + i % P) Val.nil = Y.getD i Val.nil := by rw [hii]
      exact ⟨c.getD (i / P) (0, 0), u.getD (i % P) (0, 0), by rw [← hXeq]; exact hX.2 _ ha _ hb,
        by rw [← hYeq]; exact hY.2 _ ha _ hb, hdc.2 _ hmemc, hdu.2 _ hmemu⟩
    obtain ⟨out, s', n, hpost, he, hn, hstk, hoth⟩ :=
      hpw main p X Y R hlen' hdisc (ofList X :: ofList Y :: Val.int p :: R)
        rfl s Rg hRg
    refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
    · obtain ⟨zs, hout, hzlen, hper⟩ := hpost
      exact ⟨X, Y, zs, hout, hX, hY, hzlen, hper⟩
    · refine le_trans hn (le_trans ?_ hpwCost)
      have h1 : X.length * (p + 1) ^ 2 ≤ BW_bu t P p := by
        rw [hXlen]
        simp only [BW_bu]
        have h2 : t * P * (p + 1) ^ 2 ≤ (t + 1) * ((P + 1) * (p + 1) ^ 2) := by
          have h3 : t * P ≤ (t + 1) * (P + 1) := Nat.mul_le_mul (Nat.le_succ t) (Nat.le_succ P)
          calc t * P * (p + 1) ^ 2 = (t * P) * (p + 1) ^ 2 := rfl
            _ ≤ ((t + 1) * (P + 1)) * (p + 1) ^ 2 := Nat.mul_le_mul_right _ h3
            _ = (t + 1) * ((P + 1) * (p + 1) ^ 2) := by ring
        have h4 : (t + 1) * ((P + 1) * (p + 1) ^ 2) ≤ (t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) :=
          Nat.mul_le_mul_left (t + 1) (Nat.le_add_right _ 1)
        have h5 : (t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) ≤
            (t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1 := Nat.le_add_right _ 1
        exact le_trans h2 (le_trans h4 h5)
      calc Kpw * (X.length * (p + 1) ^ 2) + Kpw ≤ Kpw * BW_bu t P p + Kpw :=
            Nat.add_le_add_right (Nat.mul_le_mul_left Kpw h1) Kpw
        _ ≤ 2 * Kpw * BW_bu t P p := by
            have hh : Kpw ≤ Kpw * BW_bu t P p := by
              have h := Nat.mul_le_mul_left Kpw hBU1
              rwa [mul_one] at h
            calc Kpw * BW_bu t P p + Kpw ≤ Kpw * BW_bu t P p + Kpw * BW_bu t P p :=
                  Nat.add_le_add_left hh (Kpw * BW_bu t P p)
              _ = 2 * Kpw * BW_bu t P p := by ring
  have hchain := wseq (wseq (wseq (wseq (wseq (wseq (wseq (wseq (wseq (wseq (wseq (wseq (wseq
    (wseq (wseq s1 s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16
  refine wconseq hchain ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hq
    obtain ⟨X, Y, zs, hout, hX, hY, hzlen, hper⟩ := hq
    obtain ⟨hXlen, hXget⟩ := hX
    obtain ⟨hYlen, hYget⟩ := hY
    have hzsl : zs.length = t * P := by rw [hzlen, hXlen]
    have hzcfx : ∀ i < zs.length, ∃ z : ℤ × ℤ, zs.getD i Val.nil = cfxVal z := by
      intro i hi
      obtain ⟨z1, z2, w, _, _, hz, _, _⟩ := hper i (by rw [← hzlen]; exact hi)
      exact ⟨w, hz⟩
    have hwlog : (zs.map pairOf).map cfxVal = zs := by
      rw [List.map_map]
      exact map_cfxVal_pairOf zs hzcfx
    refine ⟨hvs, ?_⟩
    refine ⟨zs.map pairOf, ?_, ?_, ?_, ?_⟩
    · rw [hout]
      simp only [cvecVal]
      rw [hwlog]
    · rw [List.length_map, hzsl]
    · refine ⟨by rw [List.length_map, hzsl], ?_⟩
      intro z hz
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv
      obtain ⟨z1, z2, w, _, _, hzw, hdisc, _⟩ := hper i (by rw [← hzlen]; exact hi)
      have h1 : pairOf v = w := by
        rw [← hvi, ← List.getD_eq_getElem _ _ hi, hzw]
        exact pairOf_cfxVal w
      rw [h1]
      exact hdisc
    · intro a ha b hb
      have h1 : a + 1 ≤ t := by omega
      have h2 : a * P + b < (a + 1) * P := by
        have he : (a + 1) * P = a * P + P := by ring
        rw [he]; omega
      have h3 : (a + 1) * P ≤ t * P := Nat.mul_le_mul_right P h1
      have hiX : a * P + b < X.length := by rw [hXlen]; exact lt_of_lt_of_le h2 h3
      obtain ⟨z1, z2, w, hX1, hY1, hZ1, hdisc, herr⟩ := hper (a * P + b) hiX
      have hz1 : z1 = c.getD a (0, 0) :=
        cfxVal_inj (by rw [← hX1]; exact hXget a ha b hb)
      have hz2 : z2 = u.getD b (0, 0) :=
        cfxVal_inj (by rw [← hY1]; exact hYget a ha b hb)
      have hi' : a * P + b < zs.length := by rw [hzsl, ← hXlen]; exact hiX
      have hwget : (zs.map pairOf).getD (a * P + b) (0, 0) = w := by
        rw [List.getD_eq_getElem (zs.map pairOf) (0, 0) (by rw [List.length_map]; exact hi')]
        rw [List.getElem_map]
        rw [← List.getD_eq_getElem zs Val.nil hi']
        rw [hZ1]
        exact pairOf_cfxVal w
      rw [hwget]
      have h4 := herr
      rw [hz1, hz2] at h4
      exact h4
  · intro vs hvs
    set x : ℕ := BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p with hxdef
    have hxle : x ≤ 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) * ((t * P) * p ^ 2)
        + 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) := by
      rw [hxdef]
      have hBU10 : BW_bu t P p ≤ 10 * ((t * P) * p ^ 2) + 1 := by
        simp only [BW_bu, pow_two]
        have ht1 : t + 1 ≤ 2 * t := by omega
        have hP1 : P + 1 ≤ 2 * P := by omega
        have hp1 : (p + 1) * (p + 1) ≤ 2 * (p * p) := by nlinarith [hp]
        have hpp : 1 ≤ P * (p * p) := one_le_mul' hP (one_le_mul' (by omega) (by omega))
        have hC : (t + 1) * ((P + 1) * ((p + 1) * (p + 1)) + 1)
            ≤ (2 * t) * ((2 * P) * (2 * (p * p)) + 1) :=
          Nat.mul_le_mul ht1 (Nat.add_le_add_right (Nat.mul_le_mul hP1 hp1) 1)
        have hfin : 8 * (t * P * (p * p)) + 2 * t ≤ 10 * (t * P * (p * p)) := by
          have hh : 2 * t ≤ 2 * (t * P * (p * p)) := by
            have h1 : 2 * t * 1 ≤ 2 * t * (P * (p * p)) := Nat.mul_le_mul_left (2 * t) hpp
            rw [mul_one] at h1
            calc 2 * t ≤ 2 * t * (P * (p * p)) := h1
              _ = 2 * (t * P * (p * p)) := by ring
          calc 8 * (t * P * (p * p)) + 2 * t ≤ 8 * (t * P * (p * p)) + 2 * (t * P * (p * p)) :=
                Nat.add_le_add_left hh _
            _ = 10 * (t * P * (p * p)) := by ring
        calc (t + 1) * ((P + 1) * ((p + 1) * (p + 1)) + 1) + 1
            ≤ (2 * t) * ((2 * P) * (2 * (p * p)) + 1) + 1 := Nat.add_le_add_right hC 1
          _ = 8 * (t * P * (p * p)) + 2 * t + 1 := by ring
          _ ≤ 10 * (t * P * (p * p)) + 1 := by omega
          _ = 10 * ((t * P) * (p * p)) + 1 := by ring
      calc BW_c Kroll Klen Kdrop Kst Ktl Kpw * BW_bu t P p
          ≤ BW_c Kroll Klen Kdrop Kst Ktl Kpw * (10 * ((t * P) * p ^ 2) + 1) :=
            Nat.mul_le_mul_left _ hBU10
        _ = 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw * ((t * P) * p ^ 2))
              + BW_c Kroll Klen Kdrop Kst Ktl Kpw := by ring
        _ ≤ 10 * ((BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) * ((t * P) * p ^ 2))
              + 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) := by
            have h1 : 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw * ((t * P) * p ^ 2))
                ≤ 10 * ((BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) * ((t * P) * p ^ 2)) :=
              Nat.mul_le_mul_left 10 (Nat.mul_le_mul_right _ (by omega))
            have h2 : BW_c Kroll Klen Kdrop Kst Ktl Kpw
                ≤ 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) := by omega
            exact Nat.add_le_add h1 h2
        _ = 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) * ((t * P) * p ^ 2)
              + 10 * (BW_c Kroll Klen Kdrop Kst Ktl Kpw + 1) := by ring
    linarith [hxle]

end Work.Transform
