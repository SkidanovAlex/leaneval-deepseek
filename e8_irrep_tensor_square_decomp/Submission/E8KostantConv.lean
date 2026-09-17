import Submission.WCFSetup
import Submission.Commons.Algebra.Lie.E8_Msub_weight_finrank
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_denom_mul_Kostant
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_C_wact
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom_support

/-!
# The Kostant series inverts the Weyl denominator (the `W`-sum form)

This file proves **(K-inv)**, the identity

  `∑_{w ∈ W} ε(w) · K(wρ - η) = [η = ρ]`   for every weight `η`,

where `K = KP` is the Kostant partition function (the number of multisets of positive roots
summing to a given weight) and `ρ` is the Weyl vector.

Equivalently: in the group algebra of the weight lattice, the Kostant series `Σ_δ K(δ) e^{-δ}` is
the inverse of the Weyl denominator `A_ρ = Σ_{w} ε(w) e^{wρ}`.

This is the last combinatorial ingredient of the Verma character identity
`A_ρ · chFun V_ν = e^{ν+ρ}`; see the roadmap in `Submission.lean` (§9).

## The proof

`E8_denom_mul_Kostant` (commons) states the coefficient form of
`(∏_{α>0}(1-e^{-α})) · (∏_{α>0}(1-e^{-α})^{-1}) = 1`:

  `Σ_{T ⊆ Φ⁺} (-1)^{|T|} · Kbr (ht γ) (γ - Σ_{α∈T} α) = [γ = 0]`,

where `Kbr N δ` is the height-bounded Kostant count.  Replacing the bounded count by the honest
`KP` (`Kbr N δ = KP δ` whenever `ht δ ≤ N`, which holds for `δ = γ - Σ_{α∈T}α`) and regrouping the
`T`-sum by the value of `Σ_{α∈T} α` turns the left side into

  `Σ_δ (Σ_{T : Σα = δ} (-1)^{|T|}) · KP (γ - δ)`.

The inner fiber sums are the coefficients `C δ` of the Weyl denominator: they vanish unless
`δ = ρ - wρ` (`E8_weyl_denom_support`) and equal `ε(w) = det(w)` there (`E8_weyl_denom`).  Since the
map `w ↦ ρ - wρ` is injective (`E8_weyl_stab_rho_trivial`), the sum becomes
`Σ_{M ∈ WG} det M · KP (γ - (ρ - Mρ))`, and with `γ = ρ - η` and `γ - (ρ - Mρ) = Mρ - η` this is
exactly the left side of (K-inv).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8KostantConv

open Commons.LinearAlgebra.Matrix.Cartan
open Submission.WCFSetup

/-- The positive roots of `E₈`, as a type. -/
abbrev PosR : Type := ↥E8posRoots.P

/-- **The Kostant partition function**: the number of multisets of positive roots summing to `δ`.
(This is definitionally the commons function `E8KostantId.KcountP`.) -/
noncomputable abbrev KP (δ : Fin 8 → ℤ) : ℕ := Commons.Algebra.Lie.E8KostantId.KcountP δ

/-- The box of multiplicity functions with entries at most `N`. -/
noncomputable def box (N : ℕ) : Finset (PosR → ℕ) :=
  Fintype.piFinset (fun _ : PosR => Finset.range (N + 1))

lemma mem_box {N : ℕ} {f : PosR → ℕ} : f ∈ box N ↔ ∀ α, f α ≤ N := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_add_one_iff]

/-- The Kostant count truncated at height `N`. -/
noncomputable def Kbr (N : ℕ) (δ : Fin 8 → ℤ) : ℕ :=
  ((box N).filter (fun f => ∑ α : PosR, f α • (α : Fin 8 → ℤ) = δ)).card

/-- The height of `∑_α f α • α` is `∑_α f α · ht α`. -/
lemma e8ht_sum_nsmul (f : PosR → ℕ) :
    E8NormTwo.e8ht (∑ α : PosR, f α • (α : Fin 8 → ℤ))
      = ∑ α : PosR, (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) := by
  change e8htHom (∑ α : PosR, f α • (α : Fin 8 → ℤ)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_nsmul, nsmul_eq_mul]
  rfl

/-- A solution to `∑ α, f α • α = δ` has every entry bounded by the height of `δ`. -/
lemma le_e8ht_of_sum_eq {δ : Fin 8 → ℤ} {f : PosR → ℕ}
    (hf : ∑ α : PosR, f α • (α : Fin 8 → ℤ) = δ) (α : PosR) :
    (f α : ℤ) ≤ E8NormTwo.e8ht δ := by
  have hsum := e8ht_sum_nsmul f
  rw [hf] at hsum
  have h1 : (f α : ℤ) * 1 ≤ (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) :=
    mul_le_mul_of_nonneg_left (one_le_e8ht_of_mem_P α.2) (by positivity)
  have h2 : (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ)
      ≤ ∑ β : PosR, (f β : ℤ) * E8NormTwo.e8ht (β : Fin 8 → ℤ) :=
    Finset.single_le_sum (f := fun β : PosR => (f β : ℤ) * E8NormTwo.e8ht (β : Fin 8 → ℤ))
      (fun β _ => mul_nonneg (by positivity)
        (le_trans (by norm_num) (one_le_e8ht_of_mem_P β.2)))
      (Finset.mem_univ α)
  linarith

/-- **The truncated Kostant count is the honest one** as soon as the truncation is above the
height of the target. -/
theorem Kbr_eq_KP (N : ℕ) (δ : Fin 8 → ℤ) (hN : E8NormTwo.e8ht δ ≤ (N : ℤ)) :
    Kbr N δ = KP δ := by
  classical
  have hbox : ∀ f : PosR → ℕ, (∑ α : PosR, f α • (α : Fin 8 → ℤ) = δ) → f ∈ box N := by
    intro f hf
    rw [mem_box]
    intro α
    have h := le_e8ht_of_sum_eq hf α
    omega
  have hcard : KP δ = Nat.card ↥((box N).filter (fun f => ∑ α : PosR, f α • (α : Fin 8 → ℤ) = δ)) := by
    rw [KP]
    refine Nat.card_congr
      ({ toFun := fun f => ⟨f.1, Finset.mem_filter.mpr ⟨hbox f.1 f.2, f.2⟩⟩
         invFun := fun g => ⟨g.1, (Finset.mem_filter.mp g.2).2⟩
         left_inv := fun f => by rfl
         right_inv := fun g => by rfl } : _ ≃ _)
  rw [Kbr, hcard, Nat.card_eq_fintype_card, Fintype.card_coe]

/-! ## The Weyl-denominator coefficient functional -/

lemma P_spec (v : Fin 8 → ℤ) :
    v ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)) ↔
      v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i := by
  rw [E8posRoots.memP]
  constructor
  · rintro ⟨hq, hv, hc⟩; exact ⟨hv, hq, hc⟩
  · rintro ⟨hv, hq, hc⟩; exact ⟨hq, hv, hc⟩

/-- The coefficient of `e^{-δ}` in the Weyl denominator `∏_{α>0}(1 - e^{-α})`. -/
noncomputable def C (δ : Fin 8 → ℤ) : ℤ :=
  ∑ T ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset,
    (if (∑ β ∈ T, β) = δ then (-1 : ℤ) ^ T.card else 0)

/-- The sum of the elements of a subset of the positive roots. -/
abbrev Fsum (T : Finset (Fin 8 → ℤ)) : Fin 8 → ℤ := ∑ β ∈ T, β

lemma Fsum_of_subset {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ E8posRoots.P) :
    0 ≤ E8NormTwo.e8ht (Fsum T) := by
  rw [Fsum, e8ht_sum]
  exact Finset.sum_nonneg (fun a ha =>
    le_trans (by norm_num) (one_le_e8ht_of_mem_P (hT ha)))

/-- The fiber sum of the signs over subsets with a prescribed root sum is the coefficient `C`. -/
lemma fiber_C (δ : Fin 8 → ℤ) :
    (∑ T ∈ (E8posRoots.P.powerset).filter (fun T => Fsum T = δ), (-1 : ℤ) ^ T.card) = C δ := by
  rw [C, Finset.sum_filter]

/-- The support of `C`: a nonzero coefficient occurs only at `δ = ρ - wρ`. -/
lemma C_eq_zero_of_not (δ : Fin 8 → ℤ)
    (h : ∀ L : List (Fin 8), wact L rhoZ ≠ rhoZ - δ) : C δ = 0 := by
  by_contra hne
  obtain ⟨L, hL⟩ := E8_weyl_denom_support _ P_spec δ (by rw [← C]; exact hne)
  exact h L hL

/-- The value of `C` at `ρ - wρ`. -/
lemma C_rho_sub_wact (L : List (Fin 8)) :
    C (rhoZ - wact L rhoZ) = (-1 : ℤ) ^ L.length :=
  E8_weyl_denom _ P_spec L

/-! ## The reindexing over the Weyl group -/

lemma inj_delta : Set.InjOn (fun M : Matrix (Fin 8) (Fin 8) ℤ => rhoV - ap M rhoV) ↑WG := by
  intro M hM M' hM' h
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  obtain ⟨L', rfl⟩ := mem_WG.mp hM'
  simp only [wactMat_ap, rhoV_eq] at h
  have h2 : wact L rhoZ = wact L' rhoZ := by
    simpa using congrArg (fun x => rhoZ - x) h
  rw [wactMat_eq_of_rho_eq h2]

lemma C_value_M (M : Matrix (Fin 8) (Fin 8) ℤ) (hM : M ∈ WG) :
    C (rhoV - ap M rhoV) = M.det := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  rw [wactMat_ap, rhoV_eq, C_rho_sub_wact, wactMat_det]

lemma det_ne_zero (M : Matrix (Fin 8) (Fin 8) ℤ) (hM : M ∈ WG) : M.det ≠ 0 := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  rw [wactMat_det]
  exact pow_ne_zero _ (by norm_num)

/-- The set of root-sums of subsets of the positive roots. -/
noncomputable def D : Finset (Fin 8 → ℤ) := (E8posRoots.P.powerset).image Fsum

lemma mem_D_of_C {δ : Fin 8 → ℤ} (h : C δ ≠ 0) : δ ∈ D := by
  by_contra hD
  refine h ?_
  rw [← fiber_C δ, Finset.sum_eq_zero]
  intro T hT
  rw [Finset.mem_filter] at hT
  exact absurd (Finset.mem_image.mpr ⟨T, hT.1, hT.2⟩ : δ ∈ D) hD

lemma D_filter_eq :
    D.filter (fun δ => C δ ≠ 0) = WG.image (fun M => rhoV - ap M rhoV) := by
  ext δ
  constructor
  · intro hδ
    rw [Finset.mem_filter] at hδ
    obtain ⟨L, hL⟩ := E8_weyl_denom_support _ P_spec δ (by rw [← C]; exact hδ.2)
    refine Finset.mem_image.mpr ⟨wactMat L, wactMat_mem L, ?_⟩
    show rhoV - ap (wactMat L) rhoV = δ
    rw [wactMat_ap, rhoV_eq, hL]
    abel
  · intro hδ
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hδ
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_D_of_C ?_
      rw [C_value_M M hM]
      exact det_ne_zero M hM
    · rw [C_value_M M hM]
      exact det_ne_zero M hM

/-- **Reindexing the fiber sum over the Weyl group.** -/
lemma D_sum_eq (A : (Fin 8 → ℤ) → ℤ) :
    (∑ δ ∈ D, C δ * A δ)
      = ∑ M ∈ WG, (M.det : ℤ) * A (rhoV - ap M rhoV) := by
  classical
  have hstep1 : (∑ δ ∈ D, C δ * A δ)
      = ∑ δ ∈ D.filter (fun δ => C δ ≠ 0), C δ * A δ := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro δ hδD hδnot
    have hz : C δ = 0 := by
      by_contra hc
      exact hδnot (Finset.mem_filter.mpr ⟨hδD, hc⟩)
    rw [hz, zero_mul]
  rw [hstep1, D_filter_eq]
  rw [Finset.sum_image (s := WG) (g := fun M => rhoV - ap M rhoV) inj_delta]
  exact Finset.sum_congr rfl (fun M hM => by rw [C_value_M M hM])

/-! ## (K-inv) -/

/-- **Regrouping the Weyl-denominator sum by the value of the root-sum.** -/
theorem denom_regroup (γ : Fin 8 → ℤ) :
    (∑ T ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset,
        (-1 : ℤ) ^ T.card * (KP (γ - Fsum T) : ℤ))
      = ∑ M ∈ WG, (M.det : ℤ) * (KP (γ - (rhoV - ap M rhoV)) : ℤ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset) (t := D)
    (g := fun T => Fsum T)
    (f := fun T => (-1 : ℤ) ^ T.card * (KP (γ - Fsum T) : ℤ))
    (fun T hT => Finset.mem_image_of_mem Fsum hT)]
  have hinner : ∀ δ : Fin 8 → ℤ,
      (∑ T ∈ ((E8posRoots.P : Finset (Fin 8 → ℤ)).powerset).filter (fun T => Fsum T = δ),
          (-1 : ℤ) ^ T.card * (KP (γ - Fsum T) : ℤ))
        = C δ * (KP (γ - δ) : ℤ) := by
    intro δ
    have h1 : (∑ T ∈ ((E8posRoots.P : Finset (Fin 8 → ℤ)).powerset).filter
          (fun T => Fsum T = δ), (-1 : ℤ) ^ T.card * (KP (γ - Fsum T) : ℤ))
        = ∑ T ∈ ((E8posRoots.P : Finset (Fin 8 → ℤ)).powerset).filter
            (fun T => Fsum T = δ), (-1 : ℤ) ^ T.card * (KP (γ - δ) : ℤ) :=
      Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_filter.mp hT).2])
    rw [h1, ← Finset.sum_mul, fiber_C]
  rw [Finset.sum_congr rfl (fun δ _ => hinner δ)]
  exact D_sum_eq (fun δ => (KP (γ - δ) : ℤ))

/-- The (C)-identity, in the honest Kostant form. -/
theorem denom_mul_KP (γ : Fin 8 → ℤ) :
    (∑ T ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset,
        (-1 : ℤ) ^ T.card * (KP (γ - Fsum T) : ℤ))
      = if γ = 0 then 1 else 0 := by
  have h := E8_denom_mul_Kostant γ
  rw [← h]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hN : E8NormTwo.e8ht (γ - Fsum T) ≤ (((E8NormTwo.e8ht γ).toNat : ℕ) : ℤ) := by
    rw [e8ht_sub, Fsum]
    have h1 : 0 ≤ E8NormTwo.e8ht (∑ β ∈ T, β) := by
      rw [e8ht_sum]
      exact Finset.sum_nonneg (fun a ha => le_trans (by norm_num)
        (one_le_e8ht_of_mem_P (Finset.mem_powerset.mp hT ha)))
    have h2 := Int.self_le_toNat (E8NormTwo.e8ht γ)
    linarith
  rw [show (KP (γ - Fsum T) : ℤ) = (Kbr ((E8NormTwo.e8ht γ).toNat) (γ - Fsum T) : ℤ) from by
    rw [Kbr_eq_KP _ _ hN]]
  rfl

/-- **The Kostant series inverts the Weyl denominator.**  For every weight `η`,

  `∑_{M ∈ W} ε(M) · K(Mρ - η) = [η = ρ]`,

where `K = KP` is the Kostant partition function. -/
theorem E8_weyl_kostant_K (η : Fin 8 → ℤ) :
    (∑ M ∈ WG, (M.det : ℤ) * (KP (ap M rhoV - η) : ℤ))
      = if η = rhoV then 1 else 0 := by
  have h2 : (∑ T ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset,
      (-1 : ℤ) ^ T.card * (KP (rhoV - η - Fsum T) : ℤ)) = if η = rhoV then 1 else 0 := by
    rw [denom_mul_KP (rhoV - η)]
    by_cases h : η = rhoV
    · rw [if_pos h, if_pos (show rhoV - η = 0 by rw [h]; simp)]
    · rw [if_neg h, if_neg (show ¬ (rhoV - η = 0) by
        intro hh; exact h (by rw [sub_eq_zero] at hh; exact hh.symm))]
  have h1 := denom_regroup (rhoV - η)
  rw [← h2, h1]
  exact Finset.sum_congr rfl (fun M _ => by
    rw [show rhoV - η - (rhoV - ap M rhoV) = ap M rhoV - η from by abel])

end Submission.E8KostantConv
