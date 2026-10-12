import Mathlib.Computability.Reduce
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6Est.Defs
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.meshInj` — a mesh injection with a *quantitative* separation bound

The box lattice `Lab N = Fin 3 → ZMod (2N+1)` (labels of the centred cube
`{-N,…,N}³`, physical momentum `2π·labVec N k/ℓ`) is injected into the model's mesh cube
`modeIdx n = Fin 3 → Fin (gridD n)`, `gridD n = (n+1)²`, whose points are
`modePos n k = meshD n • (k − gridD n/2)`, `meshD n = 2π/(n+1)`.

The injection `e` produced below satisfies the coordinatewise separation bound

`meshD n * (|labVec N k i|/σ + 1/2) ≤ |modePos n (e k) i|`  for all `k, i`,

i.e. (after cancelling `meshD n > 0`, using `gridD n = 2H`)

`|labVec N k i|/σ + 1/2 ≤ |(e k i : ℝ) − H|`.

Since `|labVec N k i| ≤ N` and `N + 2 ≤ σH`, one has `|a|/σ ≤ H − 2` for every box
coordinate `a = labVec N k i`, so the *centre-shifted* integer `H` is at distance
`≥ |a|/σ + 1/2` from any point we are allowed to use.  The construction is the natural
one: encode the integer `a` by

`enc a = H + ⌈|a|/σ + 1/2⌉` if `a ≥ 0`,  `enc a = H − ⌈|a|/σ + 1/2⌉` if `a < 0`,

which is injective on `ℤ` (the sign is read off from whether the value is `> H` or `< H`,
and `a ↦ ⌈|a|/σ + 1/2⌉` is strictly increasing because `σ ≤ 1`), and lies in
`{1, …, 2H−1} ⊂ {0, …, gridD n − 1}` whenever `|a| ≤ N`.  Applying `enc` to
`valMinAbs : ZMod (2N+1) → ℤ` coordinatewise gives the injection (coordinates are
independent, so it suffices that the single-coordinate map is injective).

This is the *combinatorial/geometric* row that the `FsMatchInj` interface of the chapter
needs in order to identify the box modes with mesh modes while keeping each box mode at
least as far from the mesh centre as its norm requires.
-/

namespace Work.BoseBogFS

/-- `2 ≤ H` from the mesh relation `N + 2 ≤ σ H` and `σ ≤ 1` (the cube `Fin (2H)` has
at least the three points `0, H-1, H+1`, so the encoding below has room). -/
private lemma H_ge_two {N H : ℕ} {σ : ℝ} (hσ1 : σ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) : 2 ≤ H := by
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have h1 : (2 : ℝ) ≤ (H : ℝ) := by nlinarith [hσ1, hHnn]
  exact_mod_cast h1

/-- The exponent map `a ↦ ⌈a/σ + 1/2⌉` is strictly increasing for `0 < σ ≤ 1`. -/
private lemma d_strict {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {a b : ℕ} (hab : a < b) :
    Nat.ceil ((a : ℝ) / σ + 1 / 2) < Nat.ceil ((b : ℝ) / σ + 1 / 2) := by
  have hxa : (0 : ℝ) ≤ (a : ℝ) / σ + 1 / 2 := by positivity
  have h1 : ((Nat.ceil ((a : ℝ) / σ + 1 / 2) : ℕ) : ℝ) < (a : ℝ) / σ + 1 / 2 + 1 :=
    Nat.ceil_lt_add_one hxa
  have hab' : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
  have hσinv : 1 ≤ 1 / σ := by rw [one_le_div hσ0]; linarith
  have h2 : (a : ℝ) / σ + 1 / 2 + 1 ≤ (b : ℝ) / σ + 1 / 2 := by
    have h3 : (a : ℝ) / σ + 1 ≤ (b : ℝ) / σ := by
      have h4 : (a : ℝ) / σ + 1 ≤ (a : ℝ) / σ + 1 / σ := by linarith
      have h5 : (a : ℝ) / σ + 1 / σ = ((a : ℝ) + 1) / σ := by rw [← add_div]
      have h6 : ((a : ℝ) + 1) / σ ≤ (b : ℝ) / σ := div_le_div_of_nonneg_right hab' hσ0.le
      linarith
    linarith
  have h7 : (b : ℝ) / σ + 1 / 2 ≤ ((Nat.ceil ((b : ℝ) / σ + 1 / 2) : ℕ) : ℝ) := Nat.le_ceil _
  have : ((Nat.ceil ((a : ℝ) / σ + 1 / 2) : ℕ) : ℝ)
      < ((Nat.ceil ((b : ℝ) / σ + 1 / 2) : ℕ) : ℝ) := lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h7
  exact_mod_cast this

/-- Injectivity of `a ↦ ⌈a/σ + 1/2⌉` for `0 < σ ≤ 1`. -/
private lemma d_inj {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    Function.Injective (fun a : ℕ => Nat.ceil ((a : ℝ) / σ + 1 / 2)) := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (ne_of_lt (d_strict hσ0 hσ1 h))
  · exact h
  · exact absurd hab.symm (ne_of_lt (d_strict hσ0 hσ1 h))

/-- `⌈a/σ + 1/2⌉ ≥ 1`: the exponent is always a *positive* shift, so the encoding never
lands on the centre `H`. -/
private lemma d_ge_one {σ : ℝ} (hσ0 : 0 < σ) (a : ℕ) :
    1 ≤ Nat.ceil ((a : ℝ) / σ + 1 / 2) := by
  have hx : (0 : ℝ) < (a : ℝ) / σ + 1 / 2 := by positivity
  have h1 : (a : ℝ) / σ + 1 / 2 ≤ ((Nat.ceil ((a : ℝ) / σ + 1 / 2) : ℕ) : ℝ) := Nat.le_ceil _
  have : (0 : ℝ) < ((Nat.ceil ((a : ℝ) / σ + 1 / 2) : ℕ) : ℝ) := lt_of_lt_of_le hx h1
  have : (0:ℕ) < Nat.ceil ((a : ℝ) / σ + 1 / 2) := by exact_mod_cast this
  omega

/-- The range bound: for `a ≤ N` and `N + 2 ≤ σ H` the exponent `⌈a/σ + 1/2⌉` is at most
`H − 1` (indeed `a/σ ≤ H − 2` and `σ ≤ 1`). -/
private lemma d_le {σ : ℝ} {N H : ℕ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) {a : ℕ} (ha : (a : ℝ) ≤ (N : ℝ)) :
    Nat.ceil ((a : ℝ) / σ + 1 / 2) ≤ H - 1 := by
  have hH2 : 2 ≤ H := H_ge_two hσ1 hrange
  have hH1 : 1 ≤ H := by omega
  rw [Nat.ceil_le, Nat.cast_sub hH1]
  push_cast
  have hA : ((N : ℝ) + 2) / σ ≤ (H : ℝ) := by
    rw [div_le_iff₀ hσ0]
    linarith [hrange, mul_comm σ (H : ℝ)]
  have hNdiv : (N : ℝ) / σ ≤ (H : ℝ) - 2 / σ := by
    have h2 : ((N : ℝ) + 2) / σ = (N : ℝ) / σ + 2 / σ := by rw [add_div]
    linarith
  have hσ2 : 2 ≤ 2 / σ := by rw [le_div_iff₀ hσ0]; linarith
  have hadiv : (a : ℝ) / σ ≤ (N : ℝ) / σ := div_le_div_of_nonneg_right ha hσ0.le
  linarith

/-- **The integer encoding**: `enc a = H ± ⌈|a|/σ + 1/2⌉`, with the sign of `a`. -/
private noncomputable def enc (H : ℕ) (σ : ℝ) (a : ℤ) : ℤ :=
  if 0 ≤ a then (H : ℤ) + ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ)
  else (H : ℤ) - ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ)

private lemma enc_of_nonneg {H : ℕ} {σ : ℝ} {a : ℤ} (ha : 0 ≤ a) :
    enc H σ a = (H : ℤ) + ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ) := by
  rw [enc, if_pos ha]

private lemma enc_of_neg {H : ℕ} {σ : ℝ} {a : ℤ} (ha : a < 0) :
    enc H σ a = (H : ℤ) - ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ) := by
  rw [enc, if_neg (not_le.mpr ha)]

/-- `enc` is injective on `ℤ` for `0 < σ ≤ 1`: the sign of the argument is recovered from
whether the value is `> H` or `< H` (the shift is always `≥ 1`), and the shift is
recovered from `a ↦ ⌈|a|/σ + 1/2⌉` together with `|a|`. -/
private lemma enc_inj {H : ℕ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    Function.Injective (enc H σ) := by
  intro a b hab
  have hia : (1:ℤ) ≤ ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ) := by
    have := d_ge_one hσ0 a.natAbs; exact_mod_cast this
  have hib : (1:ℤ) ≤ ((Nat.ceil (((b.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ) := by
    have := d_ge_one hσ0 b.natAbs; exact_mod_cast this
  rcases le_or_gt 0 a with ha | ha
  · rcases le_or_gt 0 b with hb | hb
    · rw [enc_of_nonneg ha, enc_of_nonneg hb] at hab
      have h2 : Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2)
          = Nat.ceil (((b.natAbs : ℕ) : ℝ) / σ + 1 / 2) := by omega
      have h3 : a.natAbs = b.natAbs := d_inj hσ0 hσ1 h2
      have h4 : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha
      have h5 : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb
      omega
    · rw [enc_of_nonneg ha, enc_of_neg hb] at hab
      omega
  · rcases le_or_gt 0 b with hb | hb
    · rw [enc_of_neg ha, enc_of_nonneg hb] at hab
      omega
    · rw [enc_of_neg ha, enc_of_neg hb] at hab
      have h2 : Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2)
          = Nat.ceil (((b.natAbs : ℕ) : ℝ) / σ + 1 / 2) := by omega
      have h3 : a.natAbs = b.natAbs := d_inj hσ0 hσ1 h2
      have h4 : (a.natAbs : ℤ) = -a := by
        have h := Int.natAbs_of_nonneg (show (0:ℤ) ≤ -a by omega)
        rwa [Int.natAbs_neg] at h
      have h5 : (b.natAbs : ℤ) = -b := by
        have h := Int.natAbs_of_nonneg (show (0:ℤ) ≤ -b by omega)
        rwa [Int.natAbs_neg] at h
      omega

/-- **The range of the encoding**: for `|a| ≤ N`, `enc a ∈ {1, …, 2H−1}`, in particular
`0 ≤ enc a < 2H = gridD n`. -/
private lemma enc_range {N H : ℕ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) {a : ℤ} (ha : a.natAbs ≤ N) :
    0 ≤ enc H σ a ∧ enc H σ a < (2 * H : ℤ) := by
  have hH1 : 1 ≤ H := by have := H_ge_two hσ1 hrange; omega
  have hdle : ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ) ≤ (H : ℤ) - 1 := by
    have ha' : ((a.natAbs : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast ha
    have h1 : Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) ≤ H - 1 := d_le hσ0 hσ1 hrange ha'
    have h2 : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by
      rw [Nat.cast_sub hH1]; norm_num
    calc ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ) ≤ ((H - 1 : ℕ) : ℤ) := by
          exact_mod_cast h1
      _ = (H : ℤ) - 1 := h2
  have hd1 : (1:ℤ) ≤ ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℤ) := by
    have := d_ge_one hσ0 a.natAbs; exact_mod_cast this
  rcases le_or_gt 0 a with ha0 | ha0
  · rw [enc_of_nonneg ha0]; constructor <;> omega
  · rw [enc_of_neg ha0]; constructor <;> omega

/-- **The separation of the encoding**: `enc a` is at distance exactly `⌈|a|/σ + 1/2⌉`
from the centre `H`. -/
private lemma enc_dist_eq {N H : ℕ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) {a : ℤ} (ha : a.natAbs ≤ N) :
    |(((enc H σ a).toNat : ℕ) : ℝ) - (H : ℝ)|
      = ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℝ) := by
  have hge := (enc_range hσ0 hσ1 hrange ha).1
  have e1 : (((enc H σ a).toNat : ℕ) : ℝ) = ((enc H σ a : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hge)
  rw [e1]
  rcases le_or_gt 0 a with ha0 | ha0
  · rw [enc_of_nonneg ha0]
    push_cast
    rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]
  · rw [enc_of_neg ha0]
    push_cast
    have h : ((H : ℝ) - ((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℝ)) - (H : ℝ)
        = -((Nat.ceil (((a.natAbs : ℕ) : ℝ) / σ + 1 / 2) : ℕ) : ℝ) := by ring
    rw [h, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]

/-- The one-coordinate encoding of a box label: apply `enc` to the least-absolute-value
representative, then read off the result as a mesh index. -/
private noncomputable def encIdx (N H : ℕ) (σ : ℝ) (x : ZMod (2 * N + 1)) : ℕ :=
  (enc H σ x.valMinAbs).toNat

private lemma encIdx_range {N H : ℕ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) (x : ZMod (2 * N + 1)) :
    encIdx N H σ x < 2 * H := by
  have hle : x.valMinAbs.natAbs ≤ N := by
    have := ZMod.natAbs_valMinAbs_le x; omega
  have h := (enc_range hσ0 hσ1 hrange hle)
  unfold encIdx
  omega

/-- The separation bound for the one-coordinate encoding. -/
private lemma encIdx_dist {N H : ℕ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) (x : ZMod (2 * N + 1)) :
    ((x.valMinAbs.natAbs : ℕ) : ℝ) / σ + 1 / 2
      ≤ |(((encIdx N H σ x : ℕ)) : ℝ) - (H : ℝ)| := by
  have hle : x.valMinAbs.natAbs ≤ N := by
    have := ZMod.natAbs_valMinAbs_le x; omega
  rw [encIdx, enc_dist_eq hσ0 hσ1 hrange hle]
  exact Nat.le_ceil _

/-- The one-coordinate encoding is injective (`valMinAbs` is injective and `enc` is). -/
private lemma encIdx_inj {N H : ℕ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) :
    Function.Injective (encIdx N H σ) := by
  intro x y hxy
  have hle_x : x.valMinAbs.natAbs ≤ N := by
    have := ZMod.natAbs_valMinAbs_le x; omega
  have hle_y : y.valMinAbs.natAbs ≤ N := by
    have := ZMod.natAbs_valMinAbs_le y; omega
  have hx0 := (enc_range hσ0 hσ1 hrange hle_x).1
  have hy0 := (enc_range hσ0 hσ1 hrange hle_y).1
  have h1 : (((enc H σ x.valMinAbs).toNat : ℕ) : ℤ) = enc H σ x.valMinAbs := Int.toNat_of_nonneg hx0
  have h2 : (((enc H σ y.valMinAbs).toNat : ℕ) : ℤ) = enc H σ y.valMinAbs := Int.toNat_of_nonneg hy0
  have h3 : enc H σ x.valMinAbs = enc H σ y.valMinAbs := by
    have : (encIdx N H σ x) = (encIdx N H σ y) := hxy
    unfold encIdx at this
    omega
  exact ZMod.injective_valMinAbs (enc_inj hσ0 hσ1 h3)

/-- **The mesh injection.**  If the mesh cube `gridD n = (n+1)²` has side `2H` and
`N + 2 ≤ σH` with `0 < σ ≤ 1`, then the box-lattice labels `Lab N` inject into the mesh
cube `modeIdx n` so that every coordinate of the image is at distance at least
`|labVec N k i|/σ + 1/2` (in units of the mesh `meshD n`) from the mesh centre `H`. -/
theorem meshInj {N n H : ℕ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hH : (Work.BoseB6.gridD n : ℝ) = 2 * (H : ℝ)) (hrange : (N : ℝ) + 2 ≤ σ * (H : ℝ)) :
    ∃ e : Work.BoseBoxFock.Lab N → Work.BoseB6Est.modeIdx n, Function.Injective e ∧
      ∀ k : Work.BoseBoxFock.Lab N, ∀ i : Fin 3,
        (Work.BoseB6.meshD n)
            * (|((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| / σ + 1 / 2)
          ≤ |(Work.BoseB6Est.modePos n (e k)) i| := by
  have hgrid : Work.BoseB6.gridD n = 2 * H := by
    have h := hH
    exact_mod_cast h
  let e : Work.BoseBoxFock.Lab N → Work.BoseB6Est.modeIdx n :=
    fun k i => ⟨encIdx N H σ (k i), by rw [hgrid]; exact encIdx_range hσ0 hσ1 hrange (k i)⟩
  have hmeshpos : (0 : ℝ) < Work.BoseB6.meshD n := by
    rw [Work.BoseB6.meshD]; positivity
  refine ⟨e, ?_, ?_⟩
  · intro k k' hkk'
    funext i
    have h : encIdx N H σ (k i) = encIdx N H σ (k' i) := by
      have h2 := congrArg Fin.val (congrFun hkk' i)
      simpa [e] using h2
    exact encIdx_inj hσ0 hσ1 hrange h
  · intro k i
    have hmode : (Work.BoseB6Est.modePos n (e k)) i
        = Work.BoseB6.meshD n * (((encIdx N H σ (k i) : ℕ) : ℝ) - (H : ℝ)) := by
      simp only [Work.BoseB6Est.modePos, Work.BoseBox.latticeCenter, e]
      rw [show ((Work.BoseB6.gridD n : ℕ) : ℝ) / 2 = (H : ℝ) by rw [hH]; ring]
    rw [hmode, abs_mul, abs_of_pos hmeshpos]
    apply mul_le_mul_of_nonneg_left _ hmeshpos.le
    have hlab : |(((Work.BoseBoxFock.labVec N k i : ℤ)) : ℝ)|
        = ((k i).valMinAbs.natAbs : ℝ) := by
      rw [Work.BoseBoxFock.labVec, ← Int.cast_abs, ← Nat.cast_natAbs]
    rw [hlab]
    exact encIdx_dist hσ0 hσ1 hrange (k i)

end Work.BoseBogFS
