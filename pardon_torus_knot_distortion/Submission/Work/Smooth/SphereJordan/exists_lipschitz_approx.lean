import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

namespace Work.Smooth.SphereJordan

open Set Metric
open scoped NNReal

noncomputable section

/-!
# Uniform approximation of a continuous map by a function Lipschitz on a ball

For a compact set `K ⊆ ℂ`, a continuous map `G : C(ℂ, ℂ)`, a centre `c : ℂ`, a radius `r : ℝ`
and a tolerance `ε > 0` we produce `P : ℂ → ℂ` which is Lipschitz on the closed ball
`Metric.closedBall c r` and is `ε`-close to `G` on `K`.

The construction approximates `G` on `K` by a polynomial in `z` and `z̄` (Stone–Weierstrass,
via `ContinuousMap.elemental_id_eq_top`), and observes that such a polynomial is Lipschitz on
every bounded set.
-/

/-- `Good c r f` records that `f` is Lipschitz on the closed ball `Metric.closedBall c r`
(with some constant `L`) and bounded there (by `M`). -/
private def Good (c : ℂ) (r : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ L M : NNReal, LipschitzOnWith L f (Metric.closedBall c r) ∧
    ∀ z ∈ Metric.closedBall c r, ‖f z‖ ≤ M

/-- The bound used for the identity and conjugation on `Metric.closedBall c r`. -/
private lemma norm_le_of_mem_cb (c : ℂ) (r : ℝ) {z : ℂ} (hz : z ∈ Metric.closedBall c r) :
    ‖z‖ ≤ ‖c‖ + |r| := by
  rw [mem_closedBall] at hz
  calc ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
        calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
          _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
    _ ≤ ‖c‖ + |r| := by
        have : ‖z - c‖ ≤ |r| := by
          rw [← dist_eq_norm]; exact le_trans hz (le_abs_self r)
        linarith

private lemma good_const (c : ℂ) (r : ℝ) (a : ℂ) : Good c r (fun _ => a) :=
  ⟨0, ‖a‖₊, (LipschitzWith.const a).lipschitzOnWith, fun z _ => by simp⟩

private lemma star_lipschitz : LipschitzWith 1 (star : ℂ → ℂ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [dist_star_star]; simp

private lemma good_id (c : ℂ) (r : ℝ) : Good c r (id : ℂ → ℂ) := by
  refine ⟨1, ‖c‖₊ + ‖r‖₊, (LipschitzWith.id).lipschitzOnWith, ?_⟩
  intro z hz
  have h := norm_le_of_mem_cb c r hz
  have hM : ((‖c‖₊ + ‖r‖₊ : NNReal) : ℝ) = ‖c‖ + |r| := by
    push_cast; rw [Real.norm_eq_abs]
  rw [hM]; simpa using h

private lemma good_star (c : ℂ) (r : ℝ) : Good c r (star : ℂ → ℂ) := by
  refine ⟨1, ‖c‖₊ + ‖r‖₊, star_lipschitz.lipschitzOnWith, ?_⟩
  intro z hz
  have h := norm_le_of_mem_cb c r hz
  have hM : ((‖c‖₊ + ‖r‖₊ : NNReal) : ℝ) = ‖c‖ + |r| := by
    push_cast; rw [Real.norm_eq_abs]
  rw [hM, norm_star]; exact h

private lemma good_add {c : ℂ} {r : ℝ} {f g : ℂ → ℂ} (hf : Good c r f) (hg : Good c r g) :
    Good c r (f + g) := by
  obtain ⟨Lf, Mf, hLf, hMf⟩ := hf
  obtain ⟨Lg, Mg, hLg, hMg⟩ := hg
  refine ⟨Lf + Lg, Mf + Mg, ?_, ?_⟩
  · have h : LipschitzOnWith (Lf + Lg) (fun x => f x + g x) (Metric.closedBall c r) :=
      hLf.add hLg
    exact h
  · intro z hz
    calc ‖(f + g) z‖ = ‖f z + g z‖ := rfl
      _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
      _ ≤ (Mf : ℝ) + Mg := add_le_add (hMf z hz) (hMg z hz)
      _ = ↑(Mf + Mg) := by push_cast; ring

private lemma good_mul {c : ℂ} {r : ℝ} {f g : ℂ → ℂ} (hf : Good c r f) (hg : Good c r g) :
    Good c r (f * g) := by
  obtain ⟨Lf, Mf, hLf, hMf⟩ := hf
  obtain ⟨Lg, Mg, hLg, hMg⟩ := hg
  refine ⟨Lf * Mg + Lg * Mf, Mf * Mg, ?_, ?_⟩
  · rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    have hxL : ‖f x - f y‖ ≤ (Lf : ℝ) * ‖x - y‖ :=
      (lipschitzOnWith_iff_norm_sub_le.mp hLf) hx hy
    have hxL' : ‖g x - g y‖ ≤ (Lg : ℝ) * ‖x - y‖ :=
      (lipschitzOnWith_iff_norm_sub_le.mp hLg) hx hy
    have h1 : ‖f x‖ ≤ (Mf : ℝ) := hMf x hx
    have h4 : ‖g y‖ ≤ (Mg : ℝ) := hMg y hy
    calc ‖(f * g) x - (f * g) y‖ = ‖f x * g x - f y * g y‖ := rfl
      _ = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by congr 1; ring
      _ ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
      _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
      _ ≤ (Mf : ℝ) * ((Lg : ℝ) * ‖x - y‖) + ((Lf : ℝ) * ‖x - y‖) * Mg := by
            apply add_le_add
            · exact mul_le_mul h1 hxL' (norm_nonneg _) (NNReal.coe_nonneg Mf)
            · exact mul_le_mul hxL h4 (norm_nonneg _) (by positivity)
      _ = ↑(Lf * Mg + Lg * Mf) * ‖x - y‖ := by push_cast; ring
  · intro z hz
    calc ‖(f * g) z‖ = ‖f z * g z‖ := rfl
      _ = ‖f z‖ * ‖g z‖ := norm_mul _ _
      _ ≤ (Mf : ℝ) * Mg :=
            mul_le_mul (hMf z hz) (hMg z hz) (norm_nonneg _) (NNReal.coe_nonneg Mf)
      _ = ↑(Mf * Mg) := by push_cast; ring

/-- The two generators we evaluate our polynomials at: `z` and `z̄`. -/
private def gfun : Fin 2 → (ℂ → ℂ) := fun i => if i = 0 then id else star

/-- Any polynomial in `z` and `z̄` is Lipschitz on the closed ball. -/
private lemma good_aeval (c : ℂ) (r : ℝ) (p : MvPolynomial (Fin 2) ℂ) :
    Good c r (MvPolynomial.aeval gfun p) := by
  have hgen : ∀ f ∈ Set.range gfun, Good c r f := by
    rintro f ⟨i, rfl⟩
    fin_cases i
    · simpa [gfun] using good_id c r
    · simpa [gfun] using good_star c r
  have hAd : ∀ f ∈ Algebra.adjoin ℂ (Set.range gfun), Good c r f := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap a => change Good c r (fun _ => a); exact good_const c r a
    | add x y hx hy hx' hy' => exact good_add hx' hy'
    | mul x y hx hy hx' hy' => exact good_mul hx' hy'
  exact hAd _ (by rw [Algebra.adjoin_range_eq_range_aeval]; exact Set.mem_range_self p)

theorem exists_lipschitz_approx {K : Set ℂ} (hK : IsCompact K) (G : C(ℂ, ℂ)) (c : ℂ) (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ → ℂ, (∃ L : NNReal, LipschitzOnWith L P (Metric.closedBall c r)) ∧
      (∀ z ∈ K, ‖P z - G z‖ ≤ ε) := by
  haveI hcomp : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  -- The two generators on `K`: the inclusion `z ↦ z` and its conjugate.
  let gK0 : C(↥K, ℂ) := ContinuousMap.restrict K (ContinuousMap.id ℂ)
  let gK : Fin 2 → C(↥K, ℂ) := fun i => if i = 0 then gK0 else star gK0
  let Ψ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] C(↥K, ℂ) := MvPolynomial.aeval gK
  have hrange : Set.range gK = ({gK0} : Set C(↥K, ℂ)) ∪ star ({gK0} : Set C(↥K, ℂ)) := by
    ext f
    rw [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; simp [gK]
      · right; rw [Set.mem_star]; simp [gK]
    · rintro (h | h)
      · exact ⟨0, by simp [gK, h]⟩
      · rw [Set.mem_star] at h
        exact ⟨1, by
          simp only [gK]
          rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
          rw [← h, star_star]⟩
  have hAB : (StarAlgebra.adjoin ℂ ({gK0} : Set C(↥K, ℂ)) : Set C(↥K, ℂ)) = Set.range Ψ := by
    rw [← StarSubalgebra.coe_toSubalgebra, StarAlgebra.adjoin_toSubalgebra, ← hrange,
      Algebra.adjoin_range_eq_range_aeval, AlgHom.coe_range]
  -- Density of the range of `Ψ`, from the Stone–Weierstrass theorem for the elemental
  -- `ℂ`-algebra generated by the inclusion.
  have hclosed : closure (Set.range Ψ) = univ := by
    have h := ContinuousMap.elemental_id_eq_top K
    rw [StarAlgebra.elemental] at h
    have h' : closure (↑(StarAlgebra.adjoin ℂ ({gK0} : Set C(↥K, ℂ))) : Set C(↥K, ℂ)) = univ := by
      rw [← StarSubalgebra.topologicalClosure_coe, h]; rfl
    rwa [hAB] at h'
  -- A polynomial agreeing with `G` on `K` to within `ε`.
  have hmem : ContinuousMap.restrict K G ∈ closure (Set.range Ψ) := by rw [hclosed]; trivial
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨p, hp⟩ := hy
  subst hp
  refine ⟨MvPolynomial.aeval gfun p, ?_, ?_⟩
  · obtain ⟨L, M, hL, _⟩ := good_aeval c r p
    exact ⟨L, hL⟩
  · -- evaluation identity between `Ψ p` on `K` and the global polynomial `aeval gfun p`
    have hbridge : ∀ (q : MvPolynomial (Fin 2) ℂ) (z : ℂ) (hz : z ∈ K),
        (Ψ q) ⟨z, hz⟩ = (MvPolynomial.aeval gfun q) z := by
      intro q z hz
      have h1 : (ContinuousMap.evalAlgHom ℂ ℂ (⟨z, hz⟩ : ↥K)).comp Ψ
          = (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) z).comp (MvPolynomial.aeval gfun) := by
        apply MvPolynomial.algHom_ext
        intro i
        fin_cases i <;>
          simp [gK, gK0, Ψ, ContinuousMap.evalAlgHom_apply, Pi.evalAlgHom_apply, gfun]
      simpa [ContinuousMap.evalAlgHom_apply, Pi.evalAlgHom_apply] using
        DFunLike.congr_fun h1 q
    intro z hz
    rw [← hbridge p z hz]
    rw [← norm_sub_rev (G z) ((Ψ p) ⟨z, hz⟩)]
    have h2 : ‖G z - (Ψ p) ⟨z, hz⟩‖ ≤ ‖ContinuousMap.restrict K G - Ψ p‖ := by
      have hh := ContinuousMap.norm_coe_le_norm (ContinuousMap.restrict K G - Ψ p) ⟨z, hz⟩
      simpa using hh
    have h3 : ‖ContinuousMap.restrict K G - Ψ p‖ < ε := by
      have := hd
      rwa [dist_eq_norm] at this
    linarith

end

end Work.Smooth.SphereJordan
