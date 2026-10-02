import Mathlib
import Submission.Work.RatHurewicz.Triad.Basic
import Submission.Work.RatHurewicz.Triad.Helpers

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `K`-trick (tom Dieck, *Algebraic Topology*, Lemma 6.9.1)

Let `f : Iᵈ → Y` be a map and `A ⊆ Y` a subset such that, on the boundary, the `A`-preimage of `f`
lies in the region where at least `p` coordinates are `< 1/2`.  Then `f` is homotopic relative to
the boundary to a map `g` whose `A`-preimage lies in that region.

The construction is a radial push from the point `x* = (1/4,…,1/4)`: with

`ψ(z) = max_i max((z_i - 1/4)/(3/4), (1/4 - z_i)/(1/4))`  (so `ψ(z) ∈ [0,1]`, `ψ(z) = 1` for
`z ∈ ∂Iᵈ`, and `ψ(z) ≥ 1/3` as soon as some coordinate of `z` is `≥ 1/2`) and `ψ̃ = max(ψ, 1/4)`,

`h_t(z) = x* + ((1-t) + t/ψ̃(z))(z - x*)`.

Then `h_t` is continuous, `h_0 = id`, `h_t` fixes `∂Iᵈ`, maps into `Iᵈ`, and `h_1(z)_i < 1/2`
implies `z_i < 1/2`.  If some coordinate of `z` is `≥ 1/2` then `ψ(z) ≥ 1/3 ≥ 1/4`, so
`h_1(z) = x* + (z - x*)/ψ(z)` lies on `∂Iᵈ`.  For `z` with `g(z) = f(h_1(z)) ∈ A`, either all
coordinates of `z` are `< 1/2` (take `L` everything, using `p ≤ d`), or some coordinate is
`≥ 1/2`; then `h_1(z) ∈ ∂Iᵈ` and the boundary hypothesis transfers back through
`z_i ≤ h_1(z)_i` (valid for `z_i ≥ 1/4`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

noncomputable section

open Work.Stems.Cubical

/-- The coefficient measuring how far `x` is (relatively) from the reference value `1/4`, towards
`1` in the positive direction and towards `0` in the negative direction. -/
def coefR (x : I) : ℝ :=
  max (((x : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4)) (((1:ℝ)/4 - (x : ℝ)) / ((1:ℝ)/4))

/-- The `ℓ∞`-radius of `z` about the reference point `(1/4,…,1/4)`, relative to the distances
`3/4` and `1/4` to the faces `1` and `0`. -/
def psiR {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : ℝ :=
  (Finset.univ : Finset (Fin d)).sup' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun i => coefR (z i))

theorem psiR_def {d : ℕ} (hd : 1 ≤ d) (z : ICube d) :
    psiR hd z = (Finset.univ : Finset (Fin d)).sup' ⟨⟨0, hd⟩, Finset.mem_univ _⟩
      (fun i => coefR (z i)) := rfl

theorem le_psiR {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (i : Fin d) : coefR (z i) ≤ psiR hd z := by
  rw [psiR_def]
  exact (Finset.le_sup'_iff ⟨⟨0, hd⟩, Finset.mem_univ _⟩).mpr ⟨i, Finset.mem_univ i, le_rfl⟩

theorem exists_psiR_eq {d : ℕ} (hd : 1 ≤ d) (z : ICube d) :
    ∃ i : Fin d, psiR hd z = coefR (z i) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun i => coefR (z i))
  exact ⟨i, by rw [psiR_def]; exact hi⟩

theorem coefR_nonneg (x : I) : 0 ≤ coefR x := by
  rcases lt_or_ge (x : ℝ) ((1:ℝ)/4) with h | h
  · have : 0 ≤ ((1:ℝ)/4 - (x : ℝ)) / ((1:ℝ)/4) := div_nonneg (by linarith) (by norm_num)
    exact le_trans this (le_max_right _ _)
  · have : 0 ≤ ((x : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4) := div_nonneg (by linarith) (by norm_num)
    exact le_trans this (le_max_left _ _)

theorem psiR_nonneg {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : 0 ≤ psiR hd z := by
  obtain ⟨i, hi⟩ := exists_psiR_eq hd z
  rw [hi]
  exact coefR_nonneg _

theorem coefR_le_one (x : I) : coefR x ≤ 1 := by
  refine max_le ?_ ?_
  · rw [div_le_one (by norm_num : (0:ℝ) < 3/4)]
    linarith [x.2.2]
  · rw [div_le_one (by norm_num : (0:ℝ) < 1/4)]
    linarith [x.2.1]

theorem psiR_le_one {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : psiR hd z ≤ 1 := by
  rw [psiR_def]
  exact Finset.sup'_le _ _ fun i _ => coefR_le_one _

theorem continuous_coefR : Continuous coefR := by
  unfold coefR
  fun_prop

theorem continuous_psiR {d : ℕ} (hd : 1 ≤ d) : Continuous (psiR hd) :=
  Continuous.finset_sup'_apply (s := Finset.univ)
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ fun i _ => continuous_coefR.comp (continuous_apply i)

/-- The radial coordinate on the boundary is `1`. -/
theorem psiR_eq_one_of_mem_boundary {d : ℕ} (hd : 1 ≤ d) {z : ICube d}
    (hz : z ∈ Cube.boundary (Fin d)) : psiR hd z = 1 := by
  obtain ⟨i, hi⟩ := hz
  refine le_antisymm (psiR_le_one hd z) ?_
  have key : coefR (z i) = 1 := by
    rcases hi with h | h
    · have hx : ((z i : I) : ℝ) = 0 := congrArg Subtype.val h
      rw [coefR, hx, max_eq_right]
      · norm_num
      · norm_num
    · have hx : ((z i : I) : ℝ) = 1 := congrArg Subtype.val h
      rw [coefR, hx, max_eq_left]
      · norm_num
      · norm_num
  rw [← key]
  exact le_psiR hd z i

/-- If some coordinate of `z` is at least `1/2`, the radial coordinate is at least `1/3`. -/
theorem psiR_ge_of_ge_half {d : ℕ} (hd : 1 ≤ d) {z : ICube d} {i : Fin d}
    (h : (1:ℝ) / 2 ≤ (z i : ℝ)) : (1:ℝ) / 3 ≤ psiR hd z := by
  refine le_trans ?_ (le_psiR hd z i)
  rw [coefR]
  refine le_trans ?_ (le_max_left _ _)
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3/4)]
  linarith

/-- The capped radial coordinate: `ψ̃ = max(ψ, 1/4)`, inverted. -/
def delR {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : ℝ :=
  1 / max (psiR hd z) ((1:ℝ)/4)

theorem delR_denom_pos {d : ℕ} (hd : 1 ≤ d) (z : ICube d) :
    (0:ℝ) < max (psiR hd z) ((1:ℝ)/4) :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem delR_pos {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : 0 < delR hd z := by
  rw [delR]
  exact div_pos one_pos (delR_denom_pos hd z)

theorem one_le_delR {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : 1 ≤ delR hd z := by
  have hpos := delR_denom_pos hd z
  have hle : max (psiR hd z) ((1:ℝ)/4) ≤ 1 :=
    max_le (psiR_le_one hd z) (by norm_num)
  rw [delR, le_div_iff₀ hpos, one_mul]
  exact hle

theorem delR_le_four {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : delR hd z ≤ (4:ℝ) := by
  have hpos := delR_denom_pos hd z
  have h : ((1:ℝ)/4) ≤ max (psiR hd z) ((1:ℝ)/4) := le_max_right _ _
  rw [delR, div_le_iff₀ hpos]
  linarith

theorem delR_eq_inv_of_ge {d : ℕ} (hd : 1 ≤ d) {z : ICube d}
    (h : ((1:ℝ)/4) ≤ psiR hd z) : delR hd z = 1 / psiR hd z := by
  rw [delR, max_eq_left h]

theorem continuous_delR {d : ℕ} (hd : 1 ≤ d) : Continuous (delR hd) :=
  Continuous.div continuous_const ((continuous_psiR hd).max continuous_const)
    fun z => ne_of_gt (delR_denom_pos hd z)

/-- The scaling factor of the homotopy at time `t`. -/
def lamR {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (t : I) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * delR hd z

theorem continuous_lamR {d : ℕ} (hd : 1 ≤ d) :
    Continuous fun p : ICube d × I => lamR hd p.1 p.2 :=
  (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_snd).mul ((continuous_delR hd).comp continuous_fst))

theorem lamR_zero {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : lamR hd z 0 = 1 := by
  rw [lamR]; norm_num

theorem lamR_one {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : lamR hd z 1 = delR hd z := by
  rw [lamR]; norm_num

theorem one_le_lamR {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (t : I) : 1 ≤ lamR hd z t := by
  have ht0 : (0:ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hd1 : 1 ≤ delR hd z := one_le_delR hd z
  rw [lamR]
  nlinarith

theorem lamR_nonneg {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (t : I) : 0 ≤ lamR hd z t :=
  le_trans (by norm_num) (one_le_lamR hd z t)

theorem lamR_eq_one_of_mem_boundary {d : ℕ} (hd : 1 ≤ d) {z : ICube d}
    (hz : z ∈ Cube.boundary (Fin d)) (t : I) : lamR hd z t = 1 := by
  have h : psiR hd z = 1 := psiR_eq_one_of_mem_boundary hd hz
  have hd1 : delR hd z = 1 := by
    rw [delR, h, max_eq_left (by norm_num : ((1:ℝ)/4) ≤ 1)]
    norm_num
  rw [lamR, hd1]
  ring

theorem coefR_mul_three_quarters (x : I) :
    (x : ℝ) - (1:ℝ)/4 ≤ coefR x * ((3:ℝ)/4) := by
  have h := le_max_left (((x : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4))
    (((1:ℝ)/4 - (x : ℝ)) / ((1:ℝ)/4))
  have h2 : ((x : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4) * ((3:ℝ)/4) = (x : ℝ) - (1:ℝ)/4 := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ) ≤ (3:ℝ)/4)
  rw [coefR]
  linarith

theorem coefR_mul_quarter (x : I) :
    (1:ℝ)/4 - (x : ℝ) ≤ coefR x * ((1:ℝ)/4) := by
  have h := le_max_right (((x : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4))
    (((1:ℝ)/4 - (x : ℝ)) / ((1:ℝ)/4))
  have h2 : ((1:ℝ)/4 - (x : ℝ)) / ((1:ℝ)/4) * ((1:ℝ)/4) = (1:ℝ)/4 - (x : ℝ) := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
  rw [coefR]
  linarith

theorem delR_mul_psiR_le_one {d : ℕ} (hd : 1 ≤ d) (z : ICube d) :
    delR hd z * psiR hd z ≤ 1 := by
  have hpos := delR_denom_pos hd z
  have hle : psiR hd z ≤ max (psiR hd z) ((1:ℝ)/4) := le_max_left _ _
  rw [delR, div_mul_eq_mul_div, one_mul, div_le_one hpos]
  exact hle

theorem lamR_le_delR {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (t : I) :
    lamR hd z t ≤ delR hd z := by
  have ht0 : (0:ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hdel : 1 ≤ delR hd z := one_le_delR hd z
  rw [lamR]
  nlinarith

/-- The bound `lamR(z,t)·(z_i - 1/4) ∈ [-1/4, 3/4]`, i.e. the point stays in the cube. -/
theorem lamR_mul_bound {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (t : I) (i : Fin d) :
    -((1:ℝ)/4) ≤ lamR hd z t * ((z i : ℝ) - (1:ℝ)/4) ∧
      lamR hd z t * ((z i : ℝ) - (1:ℝ)/4) ≤ (3:ℝ)/4 := by
  have h1 := coefR_mul_three_quarters (z i)
  have h2 := coefR_mul_quarter (z i)
  have h3 : coefR (z i) ≤ psiR hd z := le_psiR hd z i
  have h4 : delR hd z * psiR hd z ≤ 1 := delR_mul_psiR_le_one hd z
  have h5 : lamR hd z t ≤ delR hd z := lamR_le_delR hd z t
  have h6 : 0 ≤ lamR hd z t := lamR_nonneg hd z t
  have h7 : 0 ≤ psiR hd z := psiR_nonneg hd z
  have hcore : lamR hd z t * coefR (z i) ≤ delR hd z * psiR hd z :=
    calc lamR hd z t * coefR (z i) ≤ lamR hd z t * psiR hd z :=
          mul_le_mul_of_nonneg_left h3 h6
      _ ≤ delR hd z * psiR hd z := mul_le_mul_of_nonneg_right h5 h7
  constructor
  · have h8 : lamR hd z t * ((z i : ℝ) - (1:ℝ)/4)
        ≥ lamR hd z t * (-(coefR (z i) * ((1:ℝ)/4))) := by
      refine mul_le_mul_of_nonneg_left ?_ h6
      linarith
    have h9 : lamR hd z t * (coefR (z i) * ((1:ℝ)/4)) ≤ (1:ℝ)/4 := by
      nlinarith [hcore, h4]
    nlinarith [h8, h9]
  · have h8 : lamR hd z t * ((z i : ℝ) - (1:ℝ)/4)
        ≤ lamR hd z t * (coefR (z i) * ((3:ℝ)/4)) := by
      refine mul_le_mul_of_nonneg_left ?_ h6
      linarith
    have h9 : lamR hd z t * (coefR (z i) * ((3:ℝ)/4)) ≤ (3:ℝ)/4 := by
      nlinarith [hcore, h4]
    linarith [h8, h9]

/-- The point of the cube at time `t` along the radial push. -/
def hR {d : ℕ} (hd : 1 ≤ d) (p : ICube d × I) : ICube d :=
  fun i => ⟨(1:ℝ)/4 + lamR hd p.1 p.2 * ((p.1 i : ℝ) - (1:ℝ)/4), by
    have h := lamR_mul_bound hd p.1 p.2 i
    constructor <;> linarith [h.1, h.2]⟩

theorem continuous_hR {d : ℕ} (hd : 1 ≤ d) : Continuous (hR hd) := by
  refine continuous_pi fun i => Continuous.subtype_mk ?_ _
  have ha : Continuous fun p : ICube d × I => (((p.1 i : I)) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
  exact continuous_const.add ((continuous_lamR hd).mul (ha.sub continuous_const))

/-- The radial push as a continuous map of `Iᵈ × I`. -/
def hCM {d : ℕ} (hd : 1 ≤ d) : C(ICube d × I, ICube d) := ⟨hR hd, continuous_hR hd⟩

@[simp] theorem hCM_apply {d : ℕ} (hd : 1 ≤ d) (p : ICube d × I) :
    hCM hd p = hR hd p := rfl

@[simp] theorem hR_apply {d : ℕ} (hd : 1 ≤ d) (p : ICube d × I) (i : Fin d) :
    ((hR hd p i : I) : ℝ)
      = (1:ℝ)/4 + lamR hd p.1 p.2 * ((p.1 i : ℝ) - (1:ℝ)/4) := rfl

theorem hR_zero {d : ℕ} (hd : 1 ≤ d) (z : ICube d) : hR hd (z, 0) = z := by
  funext i
  apply Subtype.ext
  rw [hR_apply, lamR_zero]
  ring

theorem hR_wall {d : ℕ} (hd : 1 ≤ d) {z : ICube d} (hz : z ∈ Cube.boundary (Fin d))
    (t : I) : hR hd (z, t) = z := by
  funext i
  apply Subtype.ext
  rw [hR_apply, lamR_eq_one_of_mem_boundary hd hz t]
  ring

/-- The key inequality: if the pushed coordinate is `< 1/2`, so was the original one. -/
theorem le_of_hR_one_lt {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (i : Fin d)
    (h : ((hR hd (z, 1) i : I) : ℝ) < 1 / 2) : (z i : ℝ) < 1 / 2 := by
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ delR hd z := one_le_delR hd z
  have h2 : ((hR hd (z, 1) i : I) : ℝ)
      = (1:ℝ)/4 + delR hd z * ((z i : ℝ) - (1:ℝ)/4) := by
    rw [hR_apply, lamR_one]
  rw [h2] at h
  nlinarith

theorem psiR_eq_or {d : ℕ} (hd : 1 ≤ d) (z : ICube d) (j : Fin d)
    (hj : psiR hd z = coefR (z j)) :
    psiR hd z = ((z j : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4) ∨
      psiR hd z = ((1:ℝ)/4 - (z j : ℝ)) / ((1:ℝ)/4) := by
  have hmax : coefR (z j)
      = max (((z j : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4))
          (((1:ℝ)/4 - (z j : ℝ)) / ((1:ℝ)/4)) := rfl
  rw [hj, hmax]
  rcases lt_or_ge (((z j : ℝ) - (1:ℝ)/4) / ((3:ℝ)/4))
      (((1:ℝ)/4 - (z j : ℝ)) / ((1:ℝ)/4)) with h | h
  · right; exact max_eq_right h.le
  · left; exact max_eq_left h

/-- If some coordinate of `z` is at least `1/2`, the pushed point lies on the boundary. -/
theorem hR_one_mem_boundary {d : ℕ} (hd : 1 ≤ d) {z : ICube d} {i : Fin d}
    (h : (1:ℝ) / 2 ≤ (z i : ℝ)) : hR hd (z, 1) ∈ Cube.boundary (Fin d) := by
  obtain ⟨j, hj⟩ := exists_psiR_eq hd z
  have hpsi : ((1:ℝ)/3) ≤ psiR hd z := psiR_ge_of_ge_half hd h
  have hpsi_pos : 0 < psiR hd z := by linarith
  have hdel : delR hd z = 1 / psiR hd z := delR_eq_inv_of_ge hd (by linarith)
  have hcoord : ((hR hd (z, 1) j : I) : ℝ)
      = (1:ℝ)/4 + (1/psiR hd z) * ((z j : ℝ) - (1:ℝ)/4) := by
    rw [hR_apply, lamR_one, hdel]
  refine ⟨j, ?_⟩
  rcases psiR_eq_or hd z j hj with heq | heq
  · right
    apply Subtype.ext
    rw [hcoord, show (z j : ℝ) - (1:ℝ)/4 = (psiR hd z) * ((3:ℝ)/4) by
      rw [heq]; field_simp]
    field_simp
    norm_num
  · left
    apply Subtype.ext
    rw [hcoord, show (z j : ℝ) - (1:ℝ)/4 = -((psiR hd z) * ((1:ℝ)/4)) by
      have h2 := heq
      field_simp at h2
      linarith]
    field_simp
    norm_num

/-- **The `K`-trick.**  If on the boundary the `A`-preimage of `f` lies where at least `p`
coordinates are `< 1/2`, then `f` can be deformed relative to the boundary so that the same holds
on the whole cube. -/
theorem kTrick {Y : Type} [TopologicalSpace Y] {d : ℕ} (p : ℕ) (hp : p ≤ d)
    (f : C(ICube d, Y)) (A : Set Y)
    (h : ∀ u : ICube d, u ∈ Cube.boundary (Fin d) → f u ∈ A →
        ∃ L : Finset (Fin d), p ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2) :
    ∃ G : C(ICube d × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ u (hu : u ∈ Cube.boundary (Fin d)) t, G (u, t) = f u) ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin d), p ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨f.comp ⟨Prod.fst, continuous_fst⟩, fun u => rfl, ?_, ?_⟩
    · intro u hu
      obtain ⟨i, -⟩ := hu
      exact i.elim0
    · intro u hA
      exact ⟨∅, by simpa using hp, by simp⟩
  · refine ⟨f.comp (hCM hd), ?_, ?_, ?_⟩
    · intro u
      show (f.comp (hCM hd)) (u, 0) = f u
      rw [ContinuousMap.comp_apply, hCM_apply, hR_zero]
    · intro u hu t
      show (f.comp (hCM hd)) (u, t) = f u
      rw [ContinuousMap.comp_apply, hCM_apply, hR_wall hd hu t]
    · intro u hA
      by_cases hall : ∃ L : Finset (Fin d), p ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2
      · exact hall
      · exfalso
        push_neg at hall
        have hex : ∃ i : Fin d, (1:ℝ)/2 ≤ (u i : ℝ) := by
          obtain ⟨i, -, hi⟩ := hall (Finset.univ) (by simpa using hp)
          exact ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hex
        have hbd : hR hd (u, 1) ∈ Cube.boundary (Fin d) := hR_one_mem_boundary hd hi
        have hmem : f (hR hd (u, 1)) ∈ A := by
          have h1 : (f.comp (hCM hd)) (u, 1) = f (hR hd (u, 1)) := by
            simp only [ContinuousMap.comp_apply, hCM_apply]
          rwa [h1] at hA
        obtain ⟨L, hL, hLmem⟩ := h (hR hd (u, 1)) hbd hmem
        obtain ⟨j, hjL, hjhalf⟩ := hall L hL
        exact absurd (le_of_hR_one_lt hd u j (hLmem j hjL)) (not_lt.mpr hjhalf)

end

end Work.RatHurewicz.Triad
