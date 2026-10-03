import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.const_add_mulT_decomp
import Submission.Work.ORHughesFree.NaturalExtension.truncGrowthDefs

universe u

namespace Work.ORHughesFree.NaturalExtension

/-- **A single polynomial witness.**  Every element `x` of `degPart R I m` is the degree-`m`
coefficient vector of a *single* polynomial element `g ∈ I`.

This is the observation that `degPart R I m` is not merely a span of coefficient vectors but the
image of the submodule `I ∩ R[t;τ]` under the `R`-linear coefficient-vector map (additivity of
`cvec` is `coeffElt_add'`, compatibility with the `R`-scalar action is `coeffElt_smul'` and
`smul_eq_single_mul'`). -/
private lemma mem_degPart_exists_single {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R]
    (I : Set (SkewL R)) (hI : IsLeftIdeal I) (hne : I.Nonempty) (m : ℕ)
    {x : Fin (m + 1) → R} (hx : x ∈ degPart R I m) :
    ∃ g ∈ I, (∀ k : ℤ, k < 0 → coeffElt g k = 0) ∧ x = cvec R m g := by
  have h0I : (0 : SkewL R) ∈ I := by
    obtain ⟨a, ha⟩ := hne
    have h := hI.2 a ha 0
    rwa [zero_mul] at h
  let T : Submodule R (Fin (m + 1) → R) :=
    { carrier := {v | ∃ g ∈ I, (∀ k : ℤ, k < 0 → coeffElt g k = 0) ∧ v = cvec R m g}
      zero_mem' := ⟨0, h0I, fun k _ => by simp [coeffElt],
        by funext i; simp [cvec, coeffElt]⟩
      add_mem' := by
        rintro v w ⟨g, hgI, hgp, rfl⟩ ⟨g', hg'I, hg'p, rfl⟩
        refine ⟨g + g', hI.1 g hgI g' hg'I, ?_, ?_⟩
        · intro k hk
          rw [coeffElt_add', hgp k hk, hg'p k hk, add_zero]
        · funext i
          simp [cvec, coeffElt_add']
      smul_mem' := by
        rintro c v ⟨g, hgI, hgp, rfl⟩
        refine ⟨c • g, ?_, ?_, ?_⟩
        · rw [smul_eq_single_mul']; exact hI.2 g hgI (SkewMonoidAlgebra.single 1 c)
        · intro k hk
          rw [coeffElt_smul', hgp k hk, mul_zero]
        · funext i
          simp [cvec, coeffElt_smul'] }
  have hle : degPart R I m ≤ T :=
    Submodule.span_le.mpr (by
      rintro v ⟨f, hfI, hfp, rfl⟩
      exact ⟨f, hfI, hfp, rfl⟩)
  exact hle hx

/-- **Structure of the "no constant term" part of the degree filtration.**  Every element `x`
of `degPart R I (k+1)` with `x 0 = 0` is the twisted shift `Fin.cons 0 (τ ∘ z)` of an element
`z ∈ degPart R I k`.

PROOF SKETCH.  `degPart R I (k+1)` is spanned by the vectors `cvec R (k+1) f` for
`f ∈ I ∩ R[t;τ]`, and `f ↦ cvec R (k+1) f` is `R`-linear, so every `x ∈ degPart R I (k+1)` is
`cvec R (k+1) g` for a *single* `g ∈ I` (`cvec` commutes with `+` and with the `R`-scalar
action `coeffElt_smul'`/`smul_eq_single_mul'`; use `Submodule.span_le`).
Then `x 0 = coeffElt g 0 = 0`, so `w := skewLaurentTinv * g ∈ I` (left ideal) is polynomial
(`coeffElt (t⁻¹ * g) j = τ⁻¹ (coeffElt g (j+1))`, so the only negative coefficient is at
`j = -1` and equals `τ⁻¹ (coeffElt g 0) = 0`).  Take `z := cvec R k w ∈ degPart R I k`; then
`g = t * w` and the coefficient formula `coeffElt_skewLaurentTmul`
(`coeffElt (t * w) j = (ofAdd 1) • coeffElt w (j-1)`) gives `x 0 = 0` and
`x (i+1) = (ofAdd 1) • z i`, i.e. `x = Fin.cons 0 (τ ∘ z)`. -/
theorem degPart_ker_eq_cons {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (I : Set (SkewL R)) (hI : IsLeftIdeal I) (hne : I.Nonempty) (k : ℕ) {x : Fin (k + 2) → R}
    (hx : x ∈ degPart R I (k + 1)) (hx0 : x 0 = 0) :
    ∃ z ∈ degPart R I k,
      x = Fin.cons 0 (fun i : Fin (k + 1) => (Multiplicative.ofAdd (1 : ℤ)) • z i) := by
  -- Every element of `degPart R I (k+1)` is the coefficient vector of a single polynomial `g ∈ I`.
  obtain ⟨g, hgI, hgp, hxg⟩ := mem_degPart_exists_single I hI hne (k + 1) hx
  -- Its constant term vanishes, since `x 0 = 0`.
  have hg0 : coeffElt g 0 = 0 := by
    have h : cvec R (k + 1) g 0 = 0 := by rw [← hxg]; exact hx0
    simpa [cvec] using h
  -- `w = t⁻¹ g` is a polynomial element of `I` with `g = t w`.
  set w : SkewL R := skewTinv * g with hwdef
  have hwI : w ∈ I := hI.2 g hgI skewTinv
  have hwp : ∀ j : ℤ, j < 0 → coeffElt w j = 0 := by
    intro j hj
    rw [hwdef, coeffElt_skewTinv_mul]
    have hj1 : j + 1 ≤ 0 := by omega
    rcases lt_or_eq_of_le hj1 with h | h
    · rw [hgp (j + 1) h, smul_zero]
    · rw [h, hg0, smul_zero]
  have hgw : g = skewLaurentT * w := by
    rw [hwdef, ← mul_assoc, skewLaurentT_mul_skewTinv, one_mul]
  refine ⟨cvec R k w, Submodule.subset_span ⟨w, hwI, hwp, rfl⟩, ?_⟩
  rw [hxg, hgw]
  -- Now unwrap the coefficient vector of `t * w` on the `Fin.cons` decomposition.
  rw [← Fin.cons_self_tail (cvec R (k + 1) (skewLaurentT * w))]
  congr 1
  · -- the constant term: `coeffElt (t * w) 0 = ofAdd 1 • coeffElt w (-1) = 0`
    rw [cvec, coeffElt_skewLaurentT_mul]
    have hk : ((0 : Fin (k+2)) : ℤ) - 1 = -1 := by simp
    rw [hk, hwp (-1) (by norm_num), smul_zero]
  · -- the `(i+1)`-st term: `coeffElt (t * w) (i+1) = ofAdd 1 • coeffElt w i`
    funext j
    show cvec R (k + 1) (skewLaurentT * w) (Fin.succ j)
      = Multiplicative.ofAdd 1 • cvec R k w j
    rw [cvec, coeffElt_skewLaurentT_mul]
    congr 1
    rw [show ((Fin.succ j : Fin (k+2)) : ℤ) - 1 = (j : ℤ) by
      rw [Fin.val_succ]; push_cast; ring]
    rfl

end Work.ORHughesFree.NaturalExtension
