import Mathlib
import Submission.Work.Coherence.All
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.Coherence
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.isChar_indFun
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.Feit.excl_aux
import Submission.Work.ZassenhausPSL2.Feit.excl_degree_support
import Submission.Work.ZassenhausPSL2.Feit.card_excl
import Submission.Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_self
import Submission.Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_ne
import Submission.Work.ZassenhausPSL2.Feit.not_excl_linear
import Submission.Work.ZassenhausPSL2.FeitCln.card_conjClasses_ge
import Submission.Work.ThmG.rankOne_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausPSL2.FeitCln

variable {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}

/-! ## Stage 1: the induction map is an isometry on the degree-zero lattice of `𝒮` -/

/-- **Gram-matrix expansion.**  If `F : ↥S → G → ℂ` has Gram matrix
`⟨F x, F y⟩ = δ_{xy} + dd` and `c`, `d` are integer coefficients whose sums vanish, then the
inner product of the two integral combinations is `∑ x, c x * d x`. -/
theorem cfInner_gram_expansion {S : Finset (↥H → ℂ)} (c d : ↥S → ℤ) (F : ↥S → G → ℂ) (dd : ℂ)
    (hgram : ∀ x y : ↥S, Work.Coherence.cfInner (F x) (F y) =
      (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0) + dd)
    (hc : (∑ x : ↥S, (c x : ℂ)) = 0) (hd : (∑ x : ↥S, (d x : ℂ)) = 0) :
    Work.Coherence.cfInner (∑ x : ↥S, (c x : ℂ) • F x) (∑ y : ↥S, (d y : ℂ) • F y)
      = ∑ x : ↥S, (c x : ℂ) * (d x : ℂ) := by
  rw [Work.Coherence.cfInner_sum_smul]
  have hdec : (∑ x : ↥S, ∑ y : ↥S, (c x : ℂ) * starRingEnd ℂ ((d y : ℂ)) *
        Work.Coherence.cfInner (F x) (F y))
      = ∑ x : ↥S, ∑ y : ↥S, (c x : ℂ) * starRingEnd ℂ ((d y : ℂ)) *
        ((if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0) + dd) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hgram x y]
  rw [hdec]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hsplit : ∀ y : ↥S, (c x : ℂ) * starRingEnd ℂ ((d y : ℂ)) *
      ((if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0) + dd)
      = (c x : ℂ) * ((d y : ℂ) * (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0))
        + (c x : ℂ) * (d y : ℂ) * dd := by
    intro y; rw [map_intCast]; ring
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_add_distrib]
  have hA : (∑ y : ↥S, (c x : ℂ) *
      ((d y : ℂ) * (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0)))
      = (c x : ℂ) * (d x : ℂ) := by
    have hin : (∑ y : ↥S, (d y : ℂ) *
        (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0)) = (d x : ℂ) := by
      rw [Finset.sum_eq_single x]
      · rw [if_pos rfl, mul_one]
      · intro y _ hy; rw [if_neg (fun hh => hy (Subtype.ext hh).symm), mul_zero]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    rw [← Finset.mul_sum, hin]
  have hB : (∑ y : ↥S, (c x : ℂ) * (d y : ℂ) * dd) = 0 := by
    have hmul : (∑ y : ↥S, (c x : ℂ) * (d y : ℂ) * dd)
        = (c x : ℂ) * dd * (∑ y : ↥S, (d y : ℂ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hmul, hd, mul_zero]
  rw [hA, hB, add_zero]

/-- **Stage 1.**  The induction map `indLinear H` preserves the character inner product on the
degree-zero part of the lattice spanned by `𝒮 = excludingKernel H Q`: the Gram matrix of the
induced characters on `𝒮` is `δ + |D|`, and the degree-zero condition kills the `|D|`-term. -/
theorem isometryOn_excludingKernel (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : IsAbelianSubgroup Q) :
    Work.Coherence.IsometryOn (excludingKernel H Q) (indLinear H) := by
  classical
  refine ⟨fun α hα β hβ => ?_⟩
  obtain ⟨c, hc, hc0⟩ := Work.Coherence.mem_zSpan0_iff_coeff.mp hα
  obtain ⟨d, hd, hd0⟩ := Work.Coherence.mem_zSpan0_iff_coeff.mp hβ
  have hdeg : ∀ x : ↥(excludingKernel H Q),
      (x : ↥H → ℂ) 1 = (Nat.card (twoPoint H t) : ℂ) :=
    fun x => (Work.ZassenhausPSL2.Feit.excl_degree_support h hz h2 hab x.2).1
  have hd0' : ((Nat.card (twoPoint H t) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := twoPoint H t)).ne'
  have hcsum : (∑ x : ↥(excludingKernel H Q), (c x : ℂ)) = 0 := by
    have h' : (∑ x : ↥(excludingKernel H Q),
        (c x : ℂ) * ((Nat.card (twoPoint H t)) : ℂ)) = 0 := by
      rw [← hc0]
      exact Finset.sum_congr rfl (fun x _ => by rw [hdeg x])
    rw [← Finset.sum_mul] at h'
    exact (mul_eq_zero.mp h').resolve_right hd0'
  have hdsum : (∑ x : ↥(excludingKernel H Q), (d x : ℂ)) = 0 := by
    have h' : (∑ x : ↥(excludingKernel H Q),
        (d x : ℂ) * ((Nat.card (twoPoint H t)) : ℂ)) = 0 := by
      rw [← hd0]
      exact Finset.sum_congr rfl (fun x _ => by rw [hdeg x])
    rw [← Finset.sum_mul] at h'
    exact (mul_eq_zero.mp h').resolve_right hd0'
  have hgram : ∀ x y : ↥(excludingKernel H Q),
      Work.Coherence.cfInner (Work.Induction.indFun H (x : ↥H → ℂ))
          (Work.Induction.indFun H (y : ↥H → ℂ))
        = (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0)
            + ((Nat.card (twoPoint H t)) : ℂ) := by
    intro x y
    by_cases hxy : (x : ↥H → ℂ) = (y : ↥H → ℂ)
    · rw [if_pos hxy, hxy]
      simpa using Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_self h hz h2 hab y.2
    · rw [if_neg hxy]
      simpa using Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_ne h hz h2 hab x.2 y.2 hxy
  have htau : ∀ (e : ↥(excludingKernel H Q) → ℤ),
      indLinear H (∑ x : ↥(excludingKernel H Q), (e x : ℂ) • (x : ↥H → ℂ))
        = ∑ x : ↥(excludingKernel H Q),
            (e x : ℂ) • Work.Induction.indFun H (x : ↥H → ℂ) := by
    intro e
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (e x : ℂ) • (x : ↥H → ℂ) = (e x : ℤ) • (x : ↥H → ℂ) from
      Int.cast_smul_eq_zsmul ℂ (e x) _, map_smul]
    exact (Int.cast_smul_eq_zsmul ℂ (e x) (Work.Induction.indFun H (x : ↥H → ℂ))).symm
  have horthsum : Work.Coherence.cfInner
      (∑ x : ↥(excludingKernel H Q), (c x : ℂ) • (x : ↥H → ℂ))
      (∑ y : ↥(excludingKernel H Q), (d y : ℂ) • (y : ↥H → ℂ))
      = ∑ x : ↥(excludingKernel H Q), (c x : ℂ) * (d x : ℂ) := by
    rw [Work.Coherence.cfInner_sum_smul]
    have horth : ∀ x y : ↥(excludingKernel H Q),
        Work.Coherence.cfInner (x : ↥H → ℂ) (y : ↥H → ℂ)
          = if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0 := by
      intro x y
      rw [Work.CharCore.cfInner_coherence]
      exact Work.CharCore.irr_orthonormal _ _
        (Work.ZassenhausPSL2.Feit.mem_excludingKernel_iff.mp x.2).1
        (Work.ZassenhausPSL2.Feit.mem_excludingKernel_iff.mp y.2).1
    have hdec : (∑ x : ↥(excludingKernel H Q), ∑ y : ↥(excludingKernel H Q),
        (c x : ℂ) * starRingEnd ℂ ((d y : ℂ)) *
          Work.Coherence.cfInner (x : ↥H → ℂ) (y : ↥H → ℂ))
        = ∑ x : ↥(excludingKernel H Q), ∑ y : ↥(excludingKernel H Q),
            (c x : ℂ) * starRingEnd ℂ ((d y : ℂ)) *
              (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [horth x y]
    rw [hdec]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hterm : ∀ y : ↥(excludingKernel H Q),
        (c x : ℂ) * starRingEnd ℂ ((d y : ℂ)) *
          (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0)
        = (c x : ℂ) * ((d y : ℂ) *
            (if (x : ↥H → ℂ) = (y : ↥H → ℂ) then (1 : ℂ) else 0)) := by
      intro y; rw [map_intCast]; ring
    rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum, Finset.sum_eq_single x]
    · rw [if_pos rfl, mul_one]
    · intro y _ hy; rw [if_neg (fun hh => hy (Subtype.ext hh).symm), mul_zero]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  rw [hc, hd, htau c, htau d,
    cfInner_gram_expansion c d
      (fun x : ↥(excludingKernel H Q) => Work.Induction.indFun H (x : ↥H → ℂ))
      ((Nat.card (twoPoint H t)) : ℂ) hgram hcsum hdsum]
  exact horthsum.symm

/-- **Stage 2.**  `𝒮 = excludingKernel H Q` is coherent for the induction map `indLinear H`
(this is Feit–Thompson Lemma 10.1 applied to the norm-`|D|+1` characters of `𝒮`). -/
theorem coherent_excludingKernel (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : IsAbelianSubgroup Q) {χ₁ : H → ℂ}
    (hχ₁ : χ₁ ∈ excludingKernel H Q) (hk : 2 ≤ (excludingKernel H Q).card) :
    Work.Coherence.Coherent (excludingKernel H Q) (indLinear H) := by
  classical
  have hIrr : ∀ x ∈ excludingKernel H Q, x ∈ Work.CharCore.Irr H :=
    fun x hx => (Work.ZassenhausPSL2.Feit.mem_excludingKernel_iff.mp hx).1
  have hdeg : ∀ x ∈ excludingKernel H Q,
      x 1 = (Nat.card (twoPoint H t) : ℂ) :=
    fun x hx => (Work.ZassenhausPSL2.Feit.excl_degree_support h hz h2 hab hx).1
  refine Work.Coherence.coherent_of_norm_two_lift (S := excludingKernel H Q)
    (τ := indLinear H) (x₀ := χ₁) ?_ hχ₁ ?_ ?_ (isometryOn_excludingKernel h hz h2 hab) ?_ ?_ hk
  · -- orthonormal
    intro x hx y hy
    rw [Work.CharCore.cfInner_coherence]
    exact Work.CharCore.irr_orthonormal x y (hIrr x hx) (hIrr y hy)
  · -- all members have the same degree
    intro x hx
    rw [hdeg x hx, hdeg χ₁ hχ₁]
  · -- the degree is non-zero
    rw [hdeg χ₁ hχ₁]
    exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := twoPoint H t)).ne'
  · -- the images of the differences are virtual characters
    intro x hx
    have hsub : indLinear H (x - χ₁)
        = Work.Induction.indFun H x - Work.Induction.indFun H χ₁ := by
      rw [map_sub]; rfl
    rw [hsub]
    exact (Work.CharCore.IsVChar_iff_coherence _).mp
      (Work.CharCore.IsVChar.sub
        (Work.Induction.isVChar_indFun (Work.CharCore.IsVChar.of_mem_Irr (hIrr x hx)))
        (Work.Induction.isVChar_indFun (Work.CharCore.IsVChar.of_mem_Irr (hIrr χ₁ hχ₁))))
  · -- the images of the differences have degree zero
    intro x hx
    have hsub : indLinear H (x - χ₁)
        = Work.Induction.indFun H x - Work.Induction.indFun H χ₁ := by
      rw [map_sub]; rfl
    rw [hsub, Pi.sub_apply, Work.Induction.indFun_apply_one, Work.Induction.indFun_apply_one,
      hdeg x hx, hdeg χ₁ hχ₁, sub_self]

/-! ## Auxiliary lemmas for Stage 3 -/

/-- `Q ≠ ⊥` in a split rank-one Zassenhaus configuration. -/
lemma Q_ne_bot_aux (h : IsSplitRankOne H Q t) : Q ≠ ⊥ := by
  intro hbot
  have htwo : twoPoint H t = H := by
    have hs : Q ⊔ twoPoint H t = H := h.sup_eq
    rw [hbot, bot_sup_eq] at hs
    exact hs
  have hodd : Odd (Nat.card (twoPoint H t)) :=
    Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
  rw [htwo] at hodd
  exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd

/-- The multiplicity of an irreducible character of `G` in `Ind_H^G θ` (`θ` irreducible on `H`)
is a natural number. -/
lemma cfInner_indFun_irr_nat {θ : H → ℂ} (hθ : θ ∈ Work.CharCore.Irr H) {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) :
    ∃ n : ℕ, Work.CharCore.cfInner (Work.Induction.indFun H θ) χ = (n : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := Work.CharCore.isChar_iff_exists_nat_coeffs.mp
    (Work.Induction.isChar_indFun (Work.CharCore.IsChar.of_mem_Irr hθ))
  refine ⟨c ⟨χ, hχ⟩, ?_⟩
  rw [hc, Work.CharCore.cfInner_sum_smul_left]
  rw [Finset.sum_eq_single (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr G))]
  · rw [Work.CharCore.irr_orthonormal _ _ (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr G)).2 hχ,
      if_pos rfl, mul_one]
  · intro b _ hb
    rw [Work.CharCore.irr_orthonormal _ _ b.2 hχ, if_neg (fun hc => hb (Subtype.ext hc)),
      mul_zero]
  · intro hb; exact absurd (Finset.mem_univ _) hb

/-- **The trivial character is the only irreducible character of `G` which is orthogonal on `H`
to every member of `𝒮 = excludingKernel H Q`.** -/
lemma eq_principal_of_orthogonal [IsSimpleGroup G] (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : IsAbelianSubgroup Q) {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G)
    (horth : ∀ θ ∈ excludingKernel H Q, Work.CharCore.cfInner (Work.Induction.indFun H θ) χ = 0) :
    χ = fun _ : G => 1 := by
  classical
  have hQ : Q ≠ ⊥ := Q_ne_bot_aux h
  have hclassχ : Work.CharCore.IsClassFun χ := Work.CharCore.isClassFun_of_mem_Irr hχ
  -- the restriction of `χ` is orthogonal to `𝒮`
  have hres : ∀ θ ∈ excludingKernel H Q,
      Work.CharCore.cfInner (Work.Induction.resFun H χ) θ = 0 := by
    intro θ hθ
    have hfr := Work.Induction.frobenius_reciprocity H θ χ hclassχ
    rw [horth θ hθ] at hfr
    rw [Work.CharCore.cfInner_conj_symm, hfr.symm, map_zero]
  -- the decomposition of the restriction
  have hdecomp : Work.Induction.resFun H χ
      = ∑ θ ∈ Work.CharCore.Irr H, (Work.CharCore.cfInner (Work.Induction.resFun H χ) θ) • θ :=
    Work.CharCore.classFun_eq_sum_irr (Work.Induction.isClassFun_resFun hclassχ)
  -- `χ` is trivial on `Q`
  have hmemker : ∀ g ∈ Q, χ g = χ 1 := by
    intro g hg
    have hg1 : χ g = ∑ θ ∈ Work.CharCore.Irr H,
        Work.CharCore.cfInner (Work.Induction.resFun H χ) θ * θ (⟨g, h.le hg⟩ : ↥H) := by
      have := congrFun hdecomp (⟨g, h.le hg⟩ : ↥H)
      simpa [Work.Induction.resFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have hone : χ 1 = ∑ θ ∈ Work.CharCore.Irr H,
        Work.CharCore.cfInner (Work.Induction.resFun H χ) θ * θ (1 : ↥H) := by
      have := congrFun hdecomp (1 : ↥H)
      simpa [Work.Induction.resFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    rw [hg1, hone]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    by_cases hθS : θ ∈ excludingKernel H Q
    · rw [hres θ hθS, zero_mul, zero_mul]
    · obtain ⟨-, htriv⟩ := Work.ZassenhausPSL2.Feit.not_excl_linear h hz h2 hab hθ hθS
      rw [htriv ⟨g, h.le hg⟩ hg, htriv 1 (by simpa using Q.one_mem)]
  have hkerle : Q ≤ Work.CharCore.irrKer χ hχ := by
    intro g hg
    rw [Work.CharCore.mem_irrKer]
    exact hmemker g hg
  have htop : Work.CharCore.irrKer χ hχ = ⊤ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ (Work.CharCore.irrKer χ hχ)
      (Work.CharCore.irrKer_normal χ hχ) with hb | ht
    · exfalso
      have : Q ≤ ⊥ := hb ▸ hkerle
      exact hQ (le_bot_iff.mp this)
    · exact ht
  have hconst : ∀ g : G, χ g = χ 1 := by
    intro g
    have hg : g ∈ Work.CharCore.irrKer χ hχ := by rw [htop]; exact Subgroup.mem_top g
    rwa [Work.CharCore.mem_irrKer] at hg
  -- degrees
  have hdeg1 : χ 1 = ((Work.CharCore.irrDeg χ : ℕ) : ℂ) :=
    Work.CharCore.irrDeg_spec hχ
  have hnorm : Work.CharCore.cfInner χ χ = (χ 1) * starRingEnd ℂ (χ 1) := by
    rw [Work.CharCore.cfInner_apply]
    have hsum : (∑ x : G, χ x * starRingEnd ℂ (χ x))
        = (Fintype.card G : ℂ) * (χ 1 * starRingEnd ℂ (χ 1)) := by
      rw [Finset.sum_congr rfl (fun x _ => by rw [hconst x]), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
      one_mul]
  have hns : Complex.normSq (χ 1) = 1 := by
    have h1 : Work.CharCore.cfInner χ χ = ((Complex.normSq (χ 1) : ℝ) : ℂ) := by
      rw [hnorm, mul_comm]
      exact (Complex.normSq_eq_conj_mul_self (z := χ 1)).symm
    rw [Work.CharCore.irr_orthonormal χ χ hχ hχ, if_pos rfl] at h1
    exact_mod_cast h1.symm
  have hns' : Complex.normSq (((Work.CharCore.irrDeg χ : ℕ) : ℝ) : ℂ) = 1 := by
    have := hns
    rw [hdeg1] at this
    simpa using this
  rw [Complex.normSq_ofReal] at hns'
  have hdegone : Work.CharCore.irrDeg χ = 1 := by
    have hpos : (0 : ℝ) ≤ (Work.CharCore.irrDeg χ : ℝ) := Nat.cast_nonneg _
    have : (Work.CharCore.irrDeg χ : ℝ) = 1 := by
      nlinarith [hns', hpos]
    exact_mod_cast this
  funext g
  rw [hconst g, hdeg1, hdegone]
  norm_num

/-- **F5 (the exceptional character).**  In a split rank-one Zassenhaus configuration with `Q` an
abelian `2`-group inside a finite simple group `G`, if `𝒮 = excludingKernel H Q` has at least two
elements then there is an irreducible character `ξ` of `G` with `⟨Ind_H^G χ₁, ξ⟩ = 1` and
`⟨Ind_H^G χ, ξ⟩ = 0` for every `χ ∈ 𝒮`, `χ ≠ χ₁` (Feit 1960, §2, Theorem 2; Peterfalvi II
Appendice XII). -/
theorem exists_exceptional {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    [IsSimpleGroup G] (h : IsSplitRankOne H Q t)
    (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q) (hab : IsAbelianSubgroup Q)
    (hk : 2 ≤ (excludingKernel H Q).card) {χ₁ : H → ℂ}
    (hχ₁ : χ₁ ∈ excludingKernel H Q) :
    ∃ ξ ∈ Work.CharCore.Irr G,
      Work.CharCore.cfInner (Work.Induction.indFun H χ₁) ξ = 1 ∧
      ∀ χ ∈ excludingKernel H Q, χ ≠ χ₁ →
        Work.CharCore.cfInner (Work.Induction.indFun H χ) ξ = 0 := by
  classical
  obtain ⟨τ', hagree, hisom, hvchar⟩ := coherent_excludingKernel h hz h2 hab hχ₁ hk
  have hIrrH : ∀ x ∈ excludingKernel H Q, x ∈ Work.CharCore.Irr H :=
    fun x hx => (Work.ZassenhausPSL2.Feit.mem_excludingKernel_iff.mp hx).1
  have hdeg : ∀ x ∈ excludingKernel H Q, x 1 = (Nat.card (twoPoint H t) : ℂ) :=
    fun x hx => (Work.ZassenhausPSL2.Feit.excl_degree_support h hz h2 hab hx).1
  -- ## the irreducible characters `ψ x` with `τ' x = ± ψ x`
  have hnormτ : ∀ x : ↥(excludingKernel H Q),
      Work.CharCore.cfInner (τ' (x : ↥H → ℂ)) (τ' (x : ↥H → ℂ)) = 1 := by
    intro x
    rw [Work.CharCore.cfInner_eq_coherence]
    rw [hisom.inner_eq (x : ↥H → ℂ) (Work.Coherence.self_mem_zSpan x.2)
      (x : ↥H → ℂ) (Work.Coherence.self_mem_zSpan x.2)]
    rw [Work.CharCore.cfInner_coherence,
      Work.CharCore.irr_orthonormal _ _ (hIrrH x x.2) (hIrrH x x.2), if_pos rfl]
  have hex : ∀ x : ↥(excludingKernel H Q), ∃ ψ : G → ℂ, ψ ∈ Work.CharCore.Irr G ∧
      (τ' (x : ↥H → ℂ) = ψ ∨ τ' (x : ↥H → ℂ) = -ψ) := by
    intro x
    obtain ⟨ψ, hψ, hcase⟩ := Work.Coherence.vchar_norm_one (hvchar _ x.2) (hnormτ x)
    exact ⟨ψ, (Work.CharCore.mem_Irr_iff_coherence).mpr hψ, hcase⟩
  choose ψ hψmem hψcase using hex
  -- ## the signs
  have hsg : ∃ sg : ↥(excludingKernel H Q) → ℂ, (∀ x : ↥(excludingKernel H Q), sg x = 1 ∨ sg x = -1) ∧
      ∀ x : ↥(excludingKernel H Q), τ' (x : ↥H → ℂ) = sg x • ψ x := by
    refine ⟨fun (x : ↥(excludingKernel H Q)) => if τ' (x : ↥H → ℂ) = ψ x then 1 else -1, ?_, ?_⟩
    · intro x; dsimp only; split_ifs <;> simp
    · intro x
      by_cases hh : τ' (x : ↥H → ℂ) = ψ x
      · simp [hh]
      · have hneg : τ' (x : ↥H → ℂ) = -ψ x := by
          rcases hψcase x with h' | h'
          · exact absurd h' hh
          · exact h'
        simp [hneg]
  obtain ⟨sg, hsg_val, hsg_spec⟩ := hsg
  have hpsi_spec : ∀ x : ↥(excludingKernel H Q), ψ x = sg x • τ' (x : ↥H → ℂ) := by
    intro x
    have h2 : sg x * sg x = 1 := by
      rcases hsg_val x with h' | h' <;> rw [h'] <;> norm_num
    rw [hsg_spec x, smul_smul, h2, one_smul]
  -- ## the `ψ x` are pairwise distinct
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    by_contra hne
    have hzero : Work.CharCore.cfInner (τ' (x : ↥H → ℂ)) (τ' (y : ↥H → ℂ)) = 0 := by
      have h1 := hisom.inner_eq (x : ↥H → ℂ) (Work.Coherence.self_mem_zSpan x.2)
        (y : ↥H → ℂ) (Work.Coherence.self_mem_zSpan y.2)
      rw [Work.CharCore.cfInner_coherence, Work.CharCore.cfInner_coherence] at h1
      rw [Work.CharCore.irr_orthonormal _ _ (hIrrH x x.2) (hIrrH y y.2),
        if_neg (fun hc => hne (Subtype.ext hc))] at h1
      exact h1
    rw [hsg_spec x, hsg_spec y, hxy, Work.CharCore.cfInner_smul_left,
      Work.CharCore.cfInner_smul_right,
      Work.CharCore.irr_orthonormal _ _ (hψmem y) (hψmem y), if_pos rfl, mul_one] at hzero
    rcases hsg_val x with hx | hx <;> rcases hsg_val y with hy | hy <;>
      · rw [hx, hy] at hzero
        norm_num at hzero
  -- ## `Δ`
  let x₀ : ↥(excludingKernel H Q) := ⟨χ₁, hχ₁⟩
  have hx₀val : (x₀ : ↥H → ℂ) = χ₁ := rfl
  set Δ : G → ℂ := fun g => Work.Induction.indFun H χ₁ g - τ' (x₀ : ↥H → ℂ) g with hΔdef
  have hΔeq : ∀ x : ↥(excludingKernel H Q), ∀ g : G,
      (Work.Induction.indFun H (x : ↥H → ℂ) - τ' (x : ↥H → ℂ)) g = Δ g := by
    intro x g
    have hmem : ((x : ↥H → ℂ) - (x₀ : ↥H → ℂ)) ∈
        Work.Coherence.ZSpan0 (excludingKernel H Q) := by
      rw [Work.Coherence.mem_zSpan0]
      refine ⟨?_, ?_⟩
      · have hmem' : (x : ↥H → ℂ) + -(x₀ : ↥H → ℂ) ∈
            Work.Coherence.ZSpan (excludingKernel H Q) :=
          (Work.Coherence.ZSpan (excludingKernel H Q)).add_mem
            (Work.Coherence.self_mem_zSpan x.2)
            ((Work.Coherence.ZSpan (excludingKernel H Q)).neg_mem
              (Work.Coherence.self_mem_zSpan x₀.2))
        rwa [sub_eq_add_neg]
      · rw [Pi.sub_apply, hdeg x x.2, hdeg x₀ x₀.2, sub_self]
    have hsub : τ' ((x : ↥H → ℂ) - (x₀ : ↥H → ℂ))
        = τ' (x : ↥H → ℂ) - τ' (x₀ : ↥H → ℂ) := map_sub τ' _ _
    have h1 : τ' ((x : ↥H → ℂ) - (x₀ : ↥H → ℂ))
        = Work.Induction.indFun H (x : ↥H → ℂ) - Work.Induction.indFun H χ₁ := by
      rw [hagree _ hmem, map_sub]; rfl
    have h3 : Work.Induction.indFun H (x : ↥H → ℂ) g - Work.Induction.indFun H χ₁ g
        = τ' (x : ↥H → ℂ) g - τ' (x₀ : ↥H → ℂ) g := by
      have h4 := congrFun (h1.symm.trans hsub) g
      simpa [Pi.sub_apply] using h4
    rw [hΔdef]
    show Work.Induction.indFun H (x : ↥H → ℂ) g - τ' (x : ↥H → ℂ) g
      = Work.Induction.indFun H χ₁ g - τ' (x₀ : ↥H → ℂ) g
    linear_combination h3
  have hfun : ∀ x : ↥(excludingKernel H Q),
      Work.Induction.indFun H (x : ↥H → ℂ) = τ' (x : ↥H → ℂ) + Δ := by
    intro x
    funext g
    have h' := hΔeq x g
    rw [Pi.sub_apply] at h'
    rw [Pi.add_apply]
    linear_combination h'
  -- ## the constant `e`
  have hR1 : ∀ y : ↥(excludingKernel H Q),
      Work.CharCore.cfInner Δ (τ' (y : ↥H → ℂ))
        + starRingEnd ℂ (Work.CharCore.cfInner Δ (τ' (y : ↥H → ℂ)))
        = (Nat.card (twoPoint H t) : ℂ) - Work.CharCore.cfInner Δ Δ := by
    intro y
    have hself : Work.CharCore.cfInner (Work.Induction.indFun H (y : ↥H → ℂ))
        (Work.Induction.indFun H (y : ↥H → ℂ)) = 1 + (Nat.card (twoPoint H t) : ℂ) :=
      Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_self h hz h2 hab y.2
    have hh : Work.CharCore.cfInner (τ' (y : ↥H → ℂ) + Δ) (τ' (y : ↥H → ℂ) + Δ)
        = 1 + (Nat.card (twoPoint H t) : ℂ) := by
      rw [← hfun y]
      exact hself
    rw [Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_add_right,
      Work.CharCore.cfInner_add_right, hnormτ y] at hh
    have hconj : Work.CharCore.cfInner (τ' (y : ↥H → ℂ)) Δ
        = starRingEnd ℂ (Work.CharCore.cfInner Δ (τ' (y : ↥H → ℂ))) :=
      Work.CharCore.cfInner_conj_symm _ _
    rw [hconj] at hh
    linear_combination hh
  have hR2 : ∀ x y : ↥(excludingKernel H Q), x ≠ y →
      starRingEnd ℂ (Work.CharCore.cfInner Δ (τ' (x : ↥H → ℂ)))
        + Work.CharCore.cfInner Δ (τ' (y : ↥H → ℂ))
        = (Nat.card (twoPoint H t) : ℂ) - Work.CharCore.cfInner Δ Δ := by
    intro x y hxy
    have hxy' : (x : ↥H → ℂ) ≠ (y : ↥H → ℂ) := fun hc => hxy (Subtype.ext hc)
    have hne : Work.CharCore.cfInner (Work.Induction.indFun H (x : ↥H → ℂ))
        (Work.Induction.indFun H (y : ↥H → ℂ)) = (Nat.card (twoPoint H t) : ℂ) :=
      Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_ne h hz h2 hab x.2 y.2 hxy'
    have hzero : Work.CharCore.cfInner (τ' (x : ↥H → ℂ)) (τ' (y : ↥H → ℂ)) = 0 := by
      have h1 := hisom.inner_eq (x : ↥H → ℂ) (Work.Coherence.self_mem_zSpan x.2)
        (y : ↥H → ℂ) (Work.Coherence.self_mem_zSpan y.2)
      rw [Work.CharCore.cfInner_coherence, Work.CharCore.cfInner_coherence] at h1
      rw [Work.CharCore.irr_orthonormal _ _ (hIrrH x x.2) (hIrrH y y.2),
        if_neg hxy'] at h1
      exact h1
    have hh : Work.CharCore.cfInner (τ' (x : ↥H → ℂ) + Δ) (τ' (y : ↥H → ℂ) + Δ)
        = (Nat.card (twoPoint H t) : ℂ) := by
      rw [← hfun x, ← hfun y]
      exact hne
    rw [Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_add_right,
      Work.CharCore.cfInner_add_right, hzero, zero_add] at hh
    have hconj : Work.CharCore.cfInner (τ' (x : ↥H → ℂ)) Δ
        = starRingEnd ℂ (Work.CharCore.cfInner Δ (τ' (x : ↥H → ℂ))) :=
      Work.CharCore.cfInner_conj_symm _ _
    rw [hconj] at hh
    linear_combination hh
  have he_const : ∀ x y : ↥(excludingKernel H Q), x ≠ y →
      Work.CharCore.cfInner Δ (τ' (x : ↥H → ℂ))
        = Work.CharCore.cfInner Δ (τ' (y : ↥H → ℂ)) := by
    intro x y hxy
    have h1 := hR1 y
    have h2 := hR2 x y hxy
    have hconj : starRingEnd ℂ (Work.CharCore.cfInner Δ (τ' (x : ↥H → ℂ)))
        = starRingEnd ℂ (Work.CharCore.cfInner Δ (τ' (y : ↥H → ℂ))) := by
      linear_combination h2 - h1
    simpa using congrArg (starRingEnd ℂ) hconj
  set e : ℂ := Work.CharCore.cfInner Δ (τ' (x₀ : ↥H → ℂ)) with hedef
  have he : ∀ x : ↥(excludingKernel H Q), Work.CharCore.cfInner Δ (τ' (x : ↥H → ℂ)) = e := by
    intro x
    by_cases hx : x = x₀
    · rw [hx, hedef]
    · rw [he_const x x₀ hx, hedef]
  -- ## `sg` is constant, by comparing degrees
  have hsg_eq : ∀ x : ↥(excludingKernel H Q), sg x = sg x₀ := by
    intro x
    have hx : sg x * ψ x 1 = sg x₀ * ψ x₀ 1 := by
      have h1 : Work.Induction.indFun H (x : ↥H → ℂ) 1 = sg x * ψ x 1 + Δ 1 := by
        rw [hfun x, hsg_spec x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h2 : Work.Induction.indFun H χ₁ 1 = sg x₀ * ψ x₀ 1 + Δ 1 := by
        rw [hfun x₀, hsg_spec x₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : Work.Induction.indFun H (x : ↥H → ℂ) 1 = Work.Induction.indFun H χ₁ 1 := by
        rw [Work.Induction.indFun_apply_one, Work.Induction.indFun_apply_one,
          hdeg x x.2, hdeg χ₁ hχ₁]
      rw [h1, h2] at h3
      exact add_right_cancel h3
    have hrex : (sg x * ψ x 1).re = (sg x₀ * ψ x₀ 1).re := by rw [hx]
    have hp : ∀ z : ↥(excludingKernel H Q), 0 < (ψ z 1).re := by
      intro z
      rw [Work.CharCore.irrDeg_spec (hψmem z), Complex.natCast_re]
      exact_mod_cast Work.CharCore.irrDeg_pos (hψmem z)
    rcases hsg_val x with hx1 | hx1 <;> rcases hsg_val x₀ with h01 | h01
    · rw [hx1, h01]
    · exfalso
      rw [hx1, h01] at hrex
      simp only [one_mul, neg_one_mul, Complex.neg_re] at hrex
      linarith [hp x, hp x₀]
    · exfalso
      rw [hx1, h01] at hrex
      simp only [one_mul, neg_one_mul, Complex.neg_re] at hrex
      linarith [hp x, hp x₀]
    · rw [hx1, h01]
  -- ## the sets `A` and `T`
  set A : Finset (G → ℂ) := Finset.univ.image ψ with hAdef
  set T : Finset (G → ℂ) := (Work.CharCore.Irr G).filter
    (fun χ => χ ∉ A ∧ χ ≠ (fun _ : G => (1 : ℂ))) with hTdef
  have hAmem : ∀ χ : G → ℂ, χ ∈ A ↔ ∃ x : ↥(excludingKernel H Q), ψ x = χ := by
    intro χ
    rw [hAdef, Finset.mem_image]
    constructor
    · rintro ⟨x, -, hx⟩; exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩; exact ⟨x, Finset.mem_univ x, hx⟩
  have hTmem : ∀ χ : G → ℂ, χ ∈ T ↔ χ ∈ Work.CharCore.Irr G ∧ χ ∉ A ∧
      χ ≠ (fun _ : G => (1 : ℂ)) := by
    intro χ; rw [hTdef, Finset.mem_filter]
  have hAcard_eq : A.card = (excludingKernel H Q).card := by
    rw [hAdef, Finset.card_image_of_injective _ hψinj, Finset.card_univ, Fintype.card_coe]
  -- ## the class count `F1`
  have hIrrCard : 1 + (excludingKernel H Q).card + Nat.card (twoPoint H t)
      ≤ (Work.CharCore.Irr G).card := by
    have hF1 := Work.ZassenhausPSL2.FeitCln.card_conjClasses_ge h hz h2 hab
    have hcard := Work.ZassenhausPSL2.Feit.card_excl h hz h2 hab
    rw [← Work.CharCore.card_irr] at hF1
    have hd0 : 0 < Nat.card (twoPoint H t) := Nat.card_pos
    have hsubst : Nat.card (twoPoint H t) + (Nat.card Q - 1)
        + Nat.card (twoPoint H t) * Nat.card (twoPoint H t)
        = (1 + (excludingKernel H Q).card + Nat.card (twoPoint H t))
            * Nat.card (twoPoint H t) := by
      rw [← hcard]; ring
    rw [hsubst] at hF1
    exact Nat.le_of_mul_le_mul_right hF1 hd0
  have hTcard : Nat.card (twoPoint H t) ≤ T.card := by
    have hle : (Work.CharCore.Irr G).card ≤ T.card + (A.card + 1) := by
      have hsub : Work.CharCore.Irr G ⊆ T ∪ (A ∪ {(fun _ : G => (1 : ℂ))}) := by
        intro ξ hξ
        by_cases hξA : ξ ∈ A
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hξA)
        · by_cases hξt : ξ = (fun _ : G => (1 : ℂ))
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ (by simp [hξt]))
          · exact Finset.mem_union_left _ ((hTmem ξ).mpr ⟨hξ, hξA, hξt⟩)
      calc (Work.CharCore.Irr G).card
          ≤ (T ∪ (A ∪ {(fun _ : G => (1 : ℂ))})).card := Finset.card_le_card hsub
        _ ≤ T.card + (A ∪ {(fun _ : G => (1 : ℂ))}).card := Finset.card_union_le _ _
        _ ≤ T.card + (A.card + 1) := by
            have h' := Finset.card_union_le A ({(fun _ : G => (1 : ℂ))} : Finset (G → ℂ))
            simp only [Finset.card_singleton] at h'
            omega
    omega
  -- ## constituents of `Δ` outside `A` and the trivial character
  have hconstT : ∀ ξ ∈ T, ∃ m : ℕ, 1 ≤ m ∧ Work.CharCore.cfInner ξ Δ = (m : ℂ) := by
    intro ξ hξ
    obtain ⟨hξIrr, hξA, hξ1⟩ := (hTmem ξ).mp hξ
    have hstep : ∀ θ ∈ excludingKernel H Q,
        Work.CharCore.cfInner ξ (Work.Induction.indFun H θ) = Work.CharCore.cfInner ξ Δ := by
      intro θ hθ
      have hτ : Work.CharCore.cfInner ξ (τ' ((⟨θ, hθ⟩ : ↥(excludingKernel H Q)) : ↥H → ℂ))
          = 0 := by
        rw [hsg_spec ⟨θ, hθ⟩]
        rcases hsg_val ⟨θ, hθ⟩ with h' | h'
        · rw [h', one_smul]
          rw [Work.CharCore.irr_orthonormal ξ (ψ ⟨θ, hθ⟩) hξIrr (hψmem ⟨θ, hθ⟩),
            if_neg (fun hc => hξA ((hAmem ξ).mpr ⟨⟨θ, hθ⟩, hc.symm⟩))]
        · rw [h', neg_one_smul, Work.CharCore.cfInner_neg_right]
          rw [Work.CharCore.irr_orthonormal ξ (ψ ⟨θ, hθ⟩) hξIrr (hψmem ⟨θ, hθ⟩),
            if_neg (fun hc => hξA ((hAmem ξ).mpr ⟨⟨θ, hθ⟩, hc.symm⟩))]
          simp
      rw [hfun ⟨θ, hθ⟩, Work.CharCore.cfInner_add_right, hτ, zero_add]
    obtain ⟨n, hn⟩ := cfInner_indFun_irr_nat (hIrrH χ₁ hχ₁) hξIrr
    have hξn : Work.CharCore.cfInner ξ (Work.Induction.indFun H χ₁) = (n : ℂ) := by
      rw [Work.CharCore.cfInner_conj_symm, hn, map_natCast]
    have hne : n ≠ 0 := by
      intro hn0
      have hzero : Work.CharCore.cfInner ξ Δ = 0 := by
        rw [← hstep χ₁ hχ₁, hξn, hn0]; norm_num
      have horth : ∀ θ ∈ excludingKernel H Q,
          Work.CharCore.cfInner (Work.Induction.indFun H θ) ξ = 0 := by
        intro θ hθ
        have h2 : Work.CharCore.cfInner ξ (Work.Induction.indFun H θ) = 0 := by
          rw [hstep θ hθ, hzero]
        rw [Work.CharCore.cfInner_conj_symm, h2, map_zero]
      exact hξ1 (eq_principal_of_orthogonal h hz h2 hab hξIrr horth)
    exact ⟨n, Nat.one_le_iff_ne_zero.mpr hne, by rw [← hstep χ₁ hχ₁]; exact hξn⟩
  -- ## the bound
  have hparseval : (Work.CharCore.cfInner Δ Δ).re
      = ∑ χ ∈ Work.CharCore.Irr G, Complex.normSq (Work.CharCore.cfInner Δ χ) := by
    have hclassΔ : Work.CharCore.IsClassFun Δ := by
      rw [hΔdef]
      exact (Work.Induction.isClassFun_indFun H χ₁).sub
        ((Work.CharCore.IsClassFun_iff_coherence _).mpr
          (Work.Coherence.IsVChar.isClassFun (hvchar x₀ x₀.2)))
    have h := Work.CharCore.classFun_eq_sum_irr hclassΔ
    have h2 : Work.CharCore.cfInner Δ Δ
        = ∑ χ ∈ Work.CharCore.Irr G,
            ((Complex.normSq (Work.CharCore.cfInner Δ χ) : ℝ) : ℂ) := by
      conv_lhs => rw [h]
      have hswap : Work.CharCore.cfInner
          (∑ χ ∈ Work.CharCore.Irr G, (Work.CharCore.cfInner Δ χ) • (χ : G → ℂ))
          (∑ χ ∈ Work.CharCore.Irr G, (Work.CharCore.cfInner Δ χ) • (χ : G → ℂ))
          = ∑ χ ∈ Work.CharCore.Irr G, ∑ η ∈ Work.CharCore.Irr G,
              (Work.CharCore.cfInner Δ χ) * starRingEnd ℂ (Work.CharCore.cfInner Δ η)
                * Work.CharCore.cfInner (χ : G → ℂ) (η : G → ℂ) :=
        Work.Coherence.cfInner_sum_smul (Work.CharCore.Irr G)
          (fun χ : G → ℂ => Work.CharCore.cfInner Δ χ) (fun χ : G → ℂ => (χ : G → ℂ))
          (fun χ : G → ℂ => Work.CharCore.cfInner Δ χ) (fun χ : G → ℂ => (χ : G → ℂ))
      rw [hswap]
      refine Finset.sum_congr rfl fun χ hχmem => ?_
      have hterm : ∀ η ∈ Work.CharCore.Irr G,
          (Work.CharCore.cfInner Δ χ) * starRingEnd ℂ (Work.CharCore.cfInner Δ η)
            * Work.CharCore.cfInner χ η
          = if χ = η then (Work.CharCore.cfInner Δ χ)
              * starRingEnd ℂ (Work.CharCore.cfInner Δ χ) else 0 := by
        intro η hη
        rw [Work.CharCore.irr_orthonormal χ η hχmem hη]
        split_ifs with hc
        · subst hc; ring
        · ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single χ]
      · rw [if_pos rfl, mul_comm]
        exact (Complex.normSq_eq_conj_mul_self (z := Work.CharCore.cfInner Δ χ)).symm
      · intro η _ hη
        rw [if_neg (Ne.symm hη)]
      · intro hh; exact absurd hχmem hh
    rw [h2, Complex.re_sum]
    exact Finset.sum_congr rfl fun χ _ => by simp
  have hminT : ∀ χ ∈ T, (1 : ℝ) ≤ Complex.normSq (Work.CharCore.cfInner Δ χ) := by
    intro χ hχ
    obtain ⟨m, hm1, hm⟩ := hconstT χ hχ
    have hconj : Work.CharCore.cfInner Δ χ = (m : ℂ) := by
      rw [Work.CharCore.cfInner_conj_symm, hm, map_natCast]
    rw [hconj, Complex.normSq_natCast]
    have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hm1', hm0]
  have hboundGen : ∀ c : ℝ, (∀ χ ∈ A, c ≤ Complex.normSq (Work.CharCore.cfInner Δ χ)) →
      (T.card : ℝ) + (A.card : ℝ) * c ≤ (Work.CharCore.cfInner Δ Δ).re := by
    intro c hc
    rw [hparseval]
    have hdisj : Disjoint T A := by
      rw [Finset.disjoint_left]
      intro χ hχT hχA
      exact ((hTmem χ).mp hχT).2.1 hχA
    have hTsub : T ⊆ Work.CharCore.Irr G := fun χ hχ => ((hTmem χ).mp hχ).1
    have hAsub : A ⊆ Work.CharCore.Irr G := fun χ hχ => by
      obtain ⟨x, hx⟩ := (hAmem χ).mp hχ
      rw [← hx]; exact hψmem x
    have h1 : (∑ χ ∈ T, (1 : ℝ))
        ≤ ∑ χ ∈ T, Complex.normSq (Work.CharCore.cfInner Δ χ) :=
      Finset.sum_le_sum (fun χ hχ => hminT χ hχ)
    have h2 : (∑ χ ∈ A, c) ≤ ∑ χ ∈ A, Complex.normSq (Work.CharCore.cfInner Δ χ) :=
      Finset.sum_le_sum (fun χ hχ => hc χ hχ)
    calc (T.card : ℝ) + (A.card : ℝ) * c
        = (∑ χ ∈ T, (1 : ℝ)) + (∑ χ ∈ A, c) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
      _ ≤ (∑ χ ∈ T, Complex.normSq (Work.CharCore.cfInner Δ χ))
            + (∑ χ ∈ A, Complex.normSq (Work.CharCore.cfInner Δ χ)) := add_le_add h1 h2
      _ = ∑ χ ∈ T ∪ A, Complex.normSq (Work.CharCore.cfInner Δ χ) := by
          rw [Finset.sum_union hdisj]
      _ ≤ ∑ χ ∈ Work.CharCore.Irr G, Complex.normSq (Work.CharCore.cfInner Δ χ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hTsub hAsub)
            (fun χ _ _ => Complex.normSq_nonneg _)
  -- ## a second element of `𝒮`
  have herase : 0 < (Finset.univ.erase x₀ : Finset ↥(excludingKernel H Q)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ, Fintype.card_coe]
    omega
  obtain ⟨x₁, hx₁mem⟩ := Finset.card_pos.mp herase
  have hx₁ne : x₁ ≠ x₀ := (Finset.mem_erase.mp hx₁mem).1
  -- ## the two cases
  rcases hsg_val x₀ with hsg0 | hsg0
  · -- ## case `sg x₀ = 1`
    have hsg_all : ∀ x : ↥(excludingKernel H Q), sg x = 1 := fun x => by rw [hsg_eq x, hsg0]
    have hDe : ∀ x : ↥(excludingKernel H Q), Work.CharCore.cfInner Δ (ψ x) = e := by
      intro x
      rw [hpsi_spec x, hsg_all x, one_smul, he x]
    have he_n : ∃ n : ℕ, e = (n : ℂ) := by
      have h1 : Work.CharCore.cfInner (Work.Induction.indFun H (x₁ : ↥H → ℂ)) (ψ x₀) = e := by
        rw [hfun x₁, Work.CharCore.cfInner_add_left, hsg_spec x₁, hsg_all x₁, one_smul]
        rw [Work.CharCore.irr_orthonormal _ _ (hψmem x₁) (hψmem x₀),
          if_neg (fun hc => hx₁ne (hψinj hc)), zero_add, hDe x₀]
      obtain ⟨m, hm⟩ := cfInner_indFun_irr_nat (hIrrH x₁ x₁.2) (hψmem x₀)
      exact ⟨m, by rw [← h1]; exact hm⟩
    obtain ⟨n, hn⟩ := he_n
    have hΔΔ : (Work.CharCore.cfInner Δ Δ).re
        = (Nat.card (twoPoint H t) : ℝ) - 2 * (n : ℝ) := by
      have hR := hR1 x₀
      rw [he x₀, hn, map_natCast] at hR
      have h : Work.CharCore.cfInner Δ Δ
          = (Nat.card (twoPoint H t) : ℂ) - 2 * (n : ℂ) := by
        linear_combination hR
      rw [h]
      simp
    have hn0 : n = 0 := by
      have hb := hboundGen 0 (fun χ _ => Complex.normSq_nonneg _)
      rw [mul_zero, add_zero] at hb
      rw [hΔΔ] at hb
      have h1 : (Nat.card (twoPoint H t) : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hTcard
      have : (n : ℝ) ≤ 0 := by linarith
      exact le_antisymm (by exact_mod_cast this) (Nat.zero_le n)
    refine ⟨ψ x₀, hψmem x₀, ?_, ?_⟩
    · have h1 : Work.CharCore.cfInner (Work.Induction.indFun H χ₁) (ψ x₀) = 1 + e := by
        rw [hfun x₀, Work.CharCore.cfInner_add_left, hsg_spec x₀, hsg_all x₀, one_smul,
          Work.CharCore.irr_orthonormal _ _ (hψmem x₀) (hψmem x₀), if_pos rfl, hDe x₀]
      rw [h1, hn, hn0]; norm_num
    · intro χ hχ hne
      have hne' : (⟨χ, hχ⟩ : ↥(excludingKernel H Q)) ≠ x₀ := by
        intro hc; exact hne (congrArg Subtype.val hc)
      have h1 : Work.CharCore.cfInner (Work.Induction.indFun H χ) (ψ x₀)
          = Work.CharCore.cfInner
              (τ' ((⟨χ, hχ⟩ : ↥(excludingKernel H Q)) : ↥H → ℂ)) (ψ x₀)
            + Work.CharCore.cfInner Δ (ψ x₀) := by
        rw [hfun ⟨χ, hχ⟩, Work.CharCore.cfInner_add_left]
      rw [h1, hDe x₀, hsg_spec ⟨χ, hχ⟩, hsg_all ⟨χ, hχ⟩, one_smul,
        Work.CharCore.irr_orthonormal _ _ (hψmem ⟨χ, hχ⟩) (hψmem x₀),
        if_neg (fun hc => hne' (hψinj hc)), zero_add, hn, hn0]
      norm_num
  · -- ## case `sg x₀ = -1`
    have hsg_all : ∀ x : ↥(excludingKernel H Q), sg x = -1 := fun x => by rw [hsg_eq x, hsg0]
    have hDe : ∀ x : ↥(excludingKernel H Q), Work.CharCore.cfInner Δ (ψ x) = -e := by
      intro x
      rw [hpsi_spec x, hsg_all x, neg_one_smul, Work.CharCore.cfInner_neg_right, he x]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -((n : ℂ)) := by
      have h1 : Work.CharCore.cfInner (Work.Induction.indFun H (x₁ : ↥H → ℂ)) (ψ x₀) = -e := by
        rw [hfun x₁, Work.CharCore.cfInner_add_left, hsg_spec x₁, hsg_all x₁, neg_one_smul,
          Work.CharCore.cfInner_neg_left,
          Work.CharCore.irr_orthonormal _ _ (hψmem x₁) (hψmem x₀),
          if_neg (fun hc => hx₁ne (hψinj hc)), neg_zero, zero_add, hDe x₀]
      obtain ⟨m, hm⟩ := cfInner_indFun_irr_nat (hIrrH x₁ x₁.2) (hψmem x₀)
      refine ⟨m, ?_⟩
      have h3 : -e = (m : ℂ) := by rw [← h1]; exact hm
      linear_combination -h3
    have hn1 : 1 ≤ n := by
      have h1 : Work.CharCore.cfInner (Work.Induction.indFun H χ₁) (ψ x₀)
          = -((1 : ℂ) + e) := by
        rw [hfun x₀, Work.CharCore.cfInner_add_left, hsg_spec x₀, hsg_all x₀, neg_one_smul,
          Work.CharCore.cfInner_neg_left,
          Work.CharCore.irr_orthonormal _ _ (hψmem x₀) (hψmem x₀), if_pos rfl, hDe x₀]
        ring
      obtain ⟨m, hm⟩ := cfInner_indFun_irr_nat (hIrrH χ₁ hχ₁) (hψmem x₀)
      have h2 : (m : ℂ) + 1 = (n : ℂ) := by
        have h3 : (m : ℂ) = -((1 : ℂ) + e) := by rw [← h1]; exact hm.symm
        rw [h3, hn]; ring
      have h3 : m + 1 = n := by exact_mod_cast h2
      omega
    have hΔΔ : (Work.CharCore.cfInner Δ Δ).re
        = (Nat.card (twoPoint H t) : ℝ) + 2 * (n : ℝ) := by
      have hR := hR1 x₀
      rw [he x₀, hn, map_neg, map_natCast] at hR
      have h : Work.CharCore.cfInner Δ Δ
          = (Nat.card (twoPoint H t) : ℂ) + 2 * (n : ℂ) := by
        linear_combination hR
      rw [h]
      simp
    have hDe' : ∀ x : ↥(excludingKernel H Q), Work.CharCore.cfInner Δ (ψ x) = (n : ℂ) := by
      intro x
      rw [hDe x, hn, neg_neg]
    have hbound := hboundGen ((n : ℝ) ^ 2) (fun χ hχ => by
      obtain ⟨x, hx⟩ := (hAmem χ).mp hχ
      rw [← hx, hDe' x, Complex.normSq_natCast]
      exact le_of_eq (by ring))
    rw [hAcard_eq, hΔΔ] at hbound
    have hkey : ((excludingKernel H Q).card : ℝ) * (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) := by
      have h1 : (Nat.card (twoPoint H t) : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hTcard
      linarith [hbound, h1]
    have hkn : ((excludingKernel H Q).card : ℝ) * (n : ℝ) ≤ 2 := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      nlinarith [hkey, hnpos]
    have hk2 : (excludingKernel H Q).card = 2 := by
      have hkn' : (excludingKernel H Q).card * n ≤ 2 := by
        have h : (((excludingKernel H Q).card * n : ℕ) : ℝ) ≤ 2 := by
          rw [Nat.cast_mul]; exact hkn
        exact_mod_cast h
      have hle : (excludingKernel H Q).card ≤ 2 := by
        have hle₂ : (excludingKernel H Q).card * 1 ≤ (excludingKernel H Q).card * n :=
          Nat.mul_le_mul_left _ hn1
        calc (excludingKernel H Q).card ≤ (excludingKernel H Q).card * n := by simpa using hle₂
          _ ≤ 2 := hkn'
      omega
    have hn1' : n = 1 := by
      have hkeyNat : 2 * n ^ 2 ≤ 2 * n := by
        have h := hkey
        rw [hk2] at h
        push_cast at h
        exact_mod_cast h
      have hle : n ≤ 1 := by
        refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < n)
        nlinarith [hkeyNat]
      omega
    refine ⟨ψ x₁, hψmem x₁, ?_, ?_⟩
    · have h1 : Work.CharCore.cfInner (Work.Induction.indFun H χ₁) (ψ x₁) = 1 := by
        rw [hfun x₀, Work.CharCore.cfInner_add_left, hsg_spec x₀, hsg_all x₀, neg_one_smul,
          Work.CharCore.cfInner_neg_left,
          Work.CharCore.irr_orthonormal _ _ (hψmem x₀) (hψmem x₁),
          if_neg (fun hc => hx₁ne (hψinj hc).symm), neg_zero, zero_add, hDe' x₁, hn1']
        norm_num
      exact h1
    · intro χ hχ hne
      have hset : ({(x₀ : ↥(excludingKernel H Q)), x₁} : Finset ↥(excludingKernel H Q))
          = Finset.univ := by
        refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
        rw [Finset.card_pair hx₁ne.symm, Finset.card_univ, Fintype.card_coe, hk2]
      have hmem : (⟨χ, hχ⟩ : ↥(excludingKernel H Q)) ∈
          ({(x₀ : ↥(excludingKernel H Q)), x₁} : Finset ↥(excludingKernel H Q)) := by
        rw [hset]; exact Finset.mem_univ _
      have hval : χ = (x₁ : ↥H → ℂ) := by
        rcases Finset.mem_insert.mp hmem with h | h
        · exfalso
          exact hne (by rw [← hx₀val]; exact Subtype.ext_iff.mp h)
        · exact congrArg Subtype.val (Finset.mem_singleton.mp h)
      rw [hval, hfun x₁, Work.CharCore.cfInner_add_left, hsg_spec x₁, hsg_all x₁,
        neg_one_smul, Work.CharCore.cfInner_neg_left,
        Work.CharCore.irr_orthonormal _ _ (hψmem x₁) (hψmem x₁), if_pos rfl]
      rw [hDe' x₁, hn1']
      norm_num

end Work.ZassenhausPSL2.FeitCln
