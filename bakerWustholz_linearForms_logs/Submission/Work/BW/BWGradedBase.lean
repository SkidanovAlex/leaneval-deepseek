import Mathlib
import Submission.Work.BW.GradedHilbDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Base lemmas for the multigraded Hilbert-function machinery

This file collects the elementary facts about the multigrading of `MR N = ℂ[X_{i,j}]` by
`Fin (N+1) →₀ ℤ` (variable `(i,j)` has weight `e_i`) that the graded prime-series argument needs:

* the weight/component dictionary between the `ℤ`-grading `wZ` and the `ℕ`-grading `mdeg`;
* the notion `MultiHomZ` of a *homogeneous* ideal for the `ℤ`-grading, equivalent to `MultiHom`;
* multiplication with a homogeneous element, and how it interacts with the graded pieces
  (`comp_mul_of_mem`), which is the technical heart of the colon computation;
* the fact that the graded pieces are finite dimensional, so that `hilbIdeal` is a `finrank`.
-/

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

/-! ## `castF` and weights -/

theorem castF_add (a b : Fin (N + 1) →₀ ℕ) : castF (a + b) = castF a + castF b := by
  ext i; simp [castF_apply]

theorem castF_zero : castF (0 : Fin (N + 1) →₀ ℕ) = 0 := by
  ext i; simp [castF_apply]

theorem castF_injective : Function.Injective (castF (N := N)) := by
  intro a b h
  ext i
  have := congrArg (fun f : Fin (N + 1) →₀ ℤ => f i) h
  simp only [castF_apply] at this
  exact_mod_cast this

theorem castF_mdeg (v : Fin (N + 1) × Fin 2) : castF (mdeg N v) = wZ N v := by
  simp [mdeg, wZ, castF, Finsupp.mapRange_single]

/-- The weight of a monomial for the `ℤ`-grading is the `castF` of its weight for the
`ℕ`-grading. -/
theorem weight_wZ (c : (Fin (N + 1) × Fin 2) →₀ ℕ) :
    Finsupp.weight (wZ N) c = castF (Finsupp.weight (mdeg N) c) := by
  induction c using Finsupp.induction with
  | zero => simp [castF_zero]
  | single_add a b f _ _ ih =>
    rw [map_add (Finsupp.weight (wZ N)), map_add (Finsupp.weight (mdeg N)), castF_add, ih,
      Finsupp.weight_single, Finsupp.weight_single, castF_smul, castF_mdeg]

/-- The `ℕ`-graded and `ℤ`-graded pieces of the polynomial ring agree. -/
theorem homPiece_eq_pieceZ (d : Fin (N + 1) →₀ ℕ) : homPiece N d = pieceZ N (castF d) := by
  ext p
  rw [homPiece, pieceZ, mem_weightedHomogeneousSubmodule, mem_weightedHomogeneousSubmodule]
  constructor
  · intro h c hc
    rw [weight_wZ, h hc]
  · intro h c hc
    exact castF_injective ((weight_wZ c).symm.trans (h hc))

/-- The weighted homogeneous component for the `ℕ`-grading `d` is the component for the
`ℤ`-grading `castF d`. -/
theorem comp_castF (d : Fin (N + 1) →₀ ℕ) (p : MR N) :
    weightedHomogeneousComponent (mdeg N) d p =
      weightedHomogeneousComponent (wZ N) (castF d) p := by
  rw [weightedHomogeneousComponent_apply, weightedHomogeneousComponent_apply]
  refine Finset.sum_congr ?_ (fun c _ => rfl)
  ext c
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ =>
    ⟨fun h => by rw [weight_wZ, h], fun h => castF_injective ((weight_wZ c).symm.trans h)⟩

/-- A component of a polynomial in a degree that is not in the image of `castF` vanishes. -/
theorem comp_eq_zero_of_not_mem_range {u : Fin (N + 1) →₀ ℤ}
    (h : ∀ d : Fin (N + 1) →₀ ℕ, castF d ≠ u) (p : MR N) :
    weightedHomogeneousComponent (wZ N) u p = 0 := by
  rw [weightedHomogeneousComponent_apply]
  have hempty : p.support.filter (fun c => Finsupp.weight (wZ N) c = u) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro c _ hc
    exact h (Finsupp.weight (mdeg N) c) ((weight_wZ c).symm.trans hc)
  rw [hempty, Finset.sum_empty]

/-- The multigraded piece of degree `u` vanishes unless `u` is an `ℕ`-multidegree. -/
theorem pieceZ_eq_bot_of_not_mem_range {u : Fin (N + 1) →₀ ℤ}
    (h : ∀ d : Fin (N + 1) →₀ ℕ, castF d ≠ u) : pieceZ N u = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [mem_pieceZ] at hp
  ext m
  by_contra hm
  exact h (Finsupp.weight (mdeg N) m) ((weight_wZ m).symm.trans (hp hm))

/-! ## Homogeneous ideals for the `ℤ`-grading -/

/-- An ideal is *multihomogeneous* for the `ℤ`-grading, i.e. closed under taking
`ℤ`-homogeneous components. -/
def MultiHomZ (N : ℕ) (J : Ideal (MR N)) : Prop :=
  ∀ p ∈ J, ∀ u : Fin (N + 1) →₀ ℤ, weightedHomogeneousComponent (wZ N) u p ∈ J

/-- The colon of an ideal by a principal ideal. -/
noncomputable abbrev colonSpan (J : Ideal (MR N)) (x : MR N) : Ideal (MR N) :=
  Submodule.colon J ↑(Ideal.span {x})

theorem mem_colonSpan {J : Ideal (MR N)} {x a : MR N} :
    a ∈ colonSpan J x ↔ a * x ∈ J :=
  Ideal.mem_colon_span_singleton

theorem multiHom_iff_multiHomZ (J : Ideal (MR N)) : MultiHom N J ↔ MultiHomZ N J := by
  constructor
  · intro hM p hp u
    by_cases h : ∃ d : Fin (N + 1) →₀ ℕ, castF d = u
    · obtain ⟨d, rfl⟩ := h
      rw [← comp_castF d p]
      exact hM p hp d
    · push_neg at h
      rw [comp_eq_zero_of_not_mem_range h]
      exact J.zero_mem
  · intro hZ p hp d
    rw [comp_castF d p]
    exact hZ p hp (castF d)

/-! ## Multiplying by a homogeneous element -/

/-- The product of homogeneous elements is homogeneous of the sum of the degrees. -/
theorem pieceZ_mul (u v : Fin (N + 1) →₀ ℤ) :
    pieceZ N u * pieceZ N v ≤ pieceZ N (u + v) :=
  weightedHomogeneousSubmodule_mul (wZ N) u v

/-- **Key computation.** Multiplication by an element homogeneous of degree `u₀` shifts the
`u`-component by `u₀`. -/
theorem comp_mul_of_mem {u₀ : Fin (N + 1) →₀ ℤ} {x : MR N} (hx : x ∈ pieceZ N u₀)
    (a : MR N) (u : Fin (N + 1) →₀ ℤ) :
    weightedHomogeneousComponent (wZ N) u (x * a) =
      x * weightedHomogeneousComponent (wZ N) (u - u₀) a := by
  classical
  have hfin : Function.HasFiniteSupport fun e => weightedHomogeneousComponent (wZ N) e a :=
    weightedHomogeneousComponent_finsupp (w := wZ N) a
  have key : weightedHomogeneousComponent (wZ N) u
        (x * ∑ᶠ m, weightedHomogeneousComponent (wZ N) m a) =
      ∑ᶠ m, weightedHomogeneousComponent (wZ N) u
        (x * weightedHomogeneousComponent (wZ N) m a) := by
    have := map_finsum ((weightedHomogeneousComponent (wZ N) u).comp (LinearMap.mulLeft ℂ x)) hfin
    simpa [LinearMap.comp_apply, LinearMap.mulLeft_apply] using this
  conv_lhs => rw [← sum_weightedHomogeneousComponent (wZ N) a]
  rw [key, finsum_eq_single _ (u - u₀)]
  · have hmem : x * weightedHomogeneousComponent (wZ N) (u - u₀) a ∈ pieceZ N (u₀ + (u - u₀)) :=
      pieceZ_mul u₀ (u - u₀)
        (Submodule.mul_mem_mul hx (weightedHomogeneousComponent_mem (wZ N) a (u - u₀)))
    rw [show u₀ + (u - u₀) = u from by abel] at hmem
    rw [weightedHomogeneousComponent_of_mem hmem]
    simp
  · intro e he
    have hmem : x * weightedHomogeneousComponent (wZ N) e a ∈ pieceZ N (u₀ + e) :=
      pieceZ_mul u₀ e (Submodule.mul_mem_mul hx (weightedHomogeneousComponent_mem (wZ N) a e))
    rw [weightedHomogeneousComponent_of_mem hmem, if_neg]
    intro hh
    exact he (by rw [hh]; abel)

/-! ## Closure of `MultiHomZ` -/

theorem MultiHomZ.sup {J J' : Ideal (MR N)} (hJ : MultiHomZ N J) (hJ' : MultiHomZ N J') :
    MultiHomZ N (J ⊔ J') := by
  intro p hp u
  obtain ⟨j, hj, j', hj', rfl⟩ := Submodule.mem_sup.mp hp
  rw [map_add]
  exact (J ⊔ J').add_mem (Submodule.mem_sup_left (hJ j hj u))
    (Submodule.mem_sup_right (hJ' j' hj' u))

theorem MultiHomZ.span_singleton {x : MR N} {u : Fin (N + 1) →₀ ℤ} (hx : x ∈ pieceZ N u) :
    MultiHomZ N (Ideal.span {x}) := by
  intro p hp v
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  rw [mul_comm a x, comp_mul_of_mem hx a v]
  exact Ideal.mem_span_singleton'.mpr ⟨_, by rw [mul_comm]⟩

/-- The colon `(J : x)` of a homogeneous ideal by a homogeneous element is homogeneous. -/
theorem MultiHomZ.colon {J : Ideal (MR N)} (hJ : MultiHomZ N J) {x : MR N}
    {u : Fin (N + 1) →₀ ℤ} (hx : x ∈ pieceZ N u) :
    MultiHomZ N (colonSpan J x) := by
  intro p hp v
  rw [mem_colonSpan] at hp ⊢
  have h := hJ (p * x) hp (v + u)
  rw [mul_comm p x, comp_mul_of_mem hx p (v + u),
    show v + u - u = v from by abel, mul_comm] at h
  exact h

/-- `J` is contained in its colon by `x`. -/
theorem le_colonSpan (J : Ideal (MR N)) (x : MR N) : J ≤ colonSpan J x := by
  intro a ha
  rw [mem_colonSpan]
  exact J.mul_mem_right x ha

/-! ## Finite dimensionality of the graded pieces -/

/-- `∑ᵢ (mdeg N v)ᵢ = 1`: the `ℕ`-weight of a variable is a unit vector. -/
theorem sum_mdeg (v : Fin (N + 1) × Fin 2) : ∑ i, mdeg N v i = 1 := by
  simp [mdeg]

/-- The total degree of a monomial of `ℕ`-multidegree `d` is the sum of the entries of `d`. -/
theorem weight_one_eq_sum_mdeg (m : (Fin (N + 1) × Fin 2) →₀ ℕ) :
    Finsupp.weight (fun _ : Fin (N + 1) × Fin 2 => (1 : ℕ)) m =
      ∑ i, Finsupp.weight (mdeg N) m i := by
  induction m using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [map_add (Finsupp.weight (fun _ : Fin (N + 1) × Fin 2 => (1 : ℕ))),
      map_add (Finsupp.weight (mdeg N)), ih, Finsupp.weight_single, Finsupp.weight_single]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finset.sum_add_distrib, smul_eq_mul]
    rw [← Finset.mul_sum, sum_mdeg a]

/-- The monomials of a given `ℕ`-multidegree span a finitely generated piece. -/
theorem homPiece_fg (d : Fin (N + 1) →₀ ℕ) : (homPiece N d).FG := by
  have hfin : {m : (Fin (N + 1) × Fin 2) →₀ ℕ | Finsupp.weight (mdeg N) m = d}.Finite :=
    (Finsupp.finite_of_nat_weight_eq (fun _ : Fin (N + 1) × Fin 2 => (1 : ℕ))
      (by intro x; simp) (∑ i, d i)).subset (by
        intro m hm
        simp only [Set.mem_setOf_eq] at hm ⊢
        rw [weight_one_eq_sum_mdeg, hm])
  rw [homPiece, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single]
  exact Submodule.fg_span (hfin.image _)

/-- The multigraded pieces of the polynomial ring are finite dimensional. -/
theorem finite_pieceZ (u : Fin (N + 1) →₀ ℤ) : Module.Finite ℂ ↥(pieceZ N u) := by
  by_cases h : ∃ d : Fin (N + 1) →₀ ℕ, castF d = u
  · obtain ⟨d, rfl⟩ := h
    rw [← homPiece_eq_pieceZ d]
    exact Module.Finite.of_fg (homPiece_fg d)
  · rw [pieceZ_eq_bot_of_not_mem_range fun d hd => h ⟨d, hd⟩]
    infer_instance

/-! ## Lengths of localizations -/

/-- Length of `R/J` localized at the prime `q`, i.e. of `S ⧸ J·S` over `S = R_q`. -/
noncomputable def locLenAt {R : Type*} [CommRing R] (q : Ideal R) (hq : q.IsPrime)
    (J : Ideal R) : ℕ∞ :=
  letI := hq
  Module.length (Localization.AtPrime q)
    (Localization.AtPrime q ⧸ J.map (algebraMap R (Localization.AtPrime q)))

theorem primLen_eq_locLenAt {R : Type*} [CommRing R] (I p : Ideal R) (hp : p.IsPrime) :
    primLen I p = locLenAt p hp I := by
  rw [primLen, dif_pos hp]
  rfl

/-- The Hilbert function of the top ideal is zero. -/
theorem hilbIdeal_top (u : Fin (N + 1) →₀ ℤ) : hilbIdeal N ⊤ u = 0 := by
  rw [hilbIdeal]
  have h : Submodule.comap (pieceZ N u).subtype
      ((⊤ : Ideal (MR N)).restrictScalars ℂ) = ⊤ := by simp
  rw [h]
  exact Module.finrank_zero_of_subsingleton

theorem locLenAt_eq_zero_of_not_le {R : Type*} [CommRing R] (q : Ideal R) (hq : q.IsPrime)
    (J : Ideal R) (h : ¬ J ≤ q) : locLenAt q hq J = 0 := by
  letI := hq
  obtain ⟨a, haJ, haq⟩ := Set.not_subset.mp h
  have hunit : IsUnit (algebraMap R (Localization.AtPrime q) a) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q a).mpr haq
  have htop : J.map (algebraMap R (Localization.AtPrime q)) = ⊤ :=
    (J.map (algebraMap R (Localization.AtPrime q))).eq_top_of_isUnit_mem
      (Ideal.mem_map_of_mem _ haJ) hunit
  rw [show locLenAt q hq J = Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ J.map (algebraMap R (Localization.AtPrime q))) from rfl, htop]
  exact Module.length_eq_zero

theorem locLenAt_self {R : Type*} [CommRing R] (q : Ideal R) (hq : q.IsPrime) :
    locLenAt q hq q = 1 := by
  letI := hq
  haveI := IsLocalization.AtPrime.isLocalRing (Localization.AtPrime q) q
  have hmax : q.map (algebraMap R (Localization.AtPrime q))
      = IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)
  rw [show locLenAt q hq q = Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ q.map (algebraMap R (Localization.AtPrime q))) from rfl, hmax,
    Module.length_eq_one_iff]
  exact isSimpleModule_iff_quot_maximal.mpr
    ⟨IsLocalRing.maximalIdeal _, IsLocalRing.maximalIdeal.isMaximal _,
      ⟨LinearEquiv.refl _ _⟩⟩

theorem sum_ite_eq_card {ι : Type*} [Fintype ι] (c : ι → Prop) [DecidablePred c] :
    (∑ i, (if c i then (1 : ℕ∞) else 0)) = ((Finset.univ.filter c).card : ℕ∞) := by
  have h : (∑ i : ι, (if c i then (1 : ℕ) else 0)) = (Finset.univ.filter c).card := by
    rw [Finset.card_filter]
  rw [← h]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by split <;> simp

end Work.BW
