import Mathlib
import Submission.NK.BrauerHasse.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HassePrinciple

open NK.BrauerHasse
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

/-! ## The cochain-level transfer -/

section TransferSetup

variable {Γ : Type u} [Group Γ] (H : Subgroup Γ)

/-- Representative of the right coset `H * γ` (right-coset transversal). -/
noncomputable def tfrRep (γ : Γ) : Γ :=
  Quotient.out (Quotient.mk'' γ : Quotient (QuotientGroup.rightRel H))

/-- The element of `H` with `γ = tfrK H γ * tfrRep H γ`. -/
noncomputable def tfrK (γ : Γ) : H :=
  ⟨γ * (tfrRep H γ)⁻¹, by
    have h := Quotient.out_eq (Quotient.mk'' γ : Quotient (QuotientGroup.rightRel H))
    have h2 : QuotientGroup.rightRel H (tfrRep H γ) γ := Quotient.exact h
    rw [QuotientGroup.rightRel_apply] at h2
    simpa [tfrRep] using h2⟩

lemma tfrK_spec (γ : Γ) : (tfrK H γ : Γ) * tfrRep H γ = γ := by
  simp [tfrK, mul_assoc]

lemma tfrRep_idem (γ : Γ) : tfrRep H (tfrRep H γ) = tfrRep H γ :=
  congrArg Quotient.out (Quotient.out_eq (Quotient.mk'' γ : Quotient (QuotientGroup.rightRel H)))

lemma tfrRep_eq_of_rel {a b : Γ} (h : QuotientGroup.rightRel H a b) :
    tfrRep H a = tfrRep H b := by
  have h2 : (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) = Quotient.mk'' b :=
    Quotient.sound h
  simp [tfrRep, h2]

lemma tfrRep_mul_left (h : H) (γ : Γ) : tfrRep H ((h : Γ) * γ) = tfrRep H γ := by
  apply tfrRep_eq_of_rel
  rw [QuotientGroup.rightRel_apply]
  have hh : γ * ((h : Γ) * γ)⁻¹ = (h : Γ)⁻¹ := by group
  rw [hh]
  exact H.inv_mem h.2

lemma tfrRep_mul_right (x γ : Γ) : tfrRep H (tfrRep H x * γ) = tfrRep H (x * γ) := by
  apply tfrRep_eq_of_rel
  rw [QuotientGroup.rightRel_apply]
  have h := Quotient.out_eq (Quotient.mk'' x : Quotient (QuotientGroup.rightRel H))
  have h2 : QuotientGroup.rightRel H (tfrRep H x) x := Quotient.exact h
  rw [QuotientGroup.rightRel_apply] at h2
  have hh : x * γ * (tfrRep H x * γ)⁻¹ = x * (tfrRep H x)⁻¹ := by group
  rw [hh]
  exact h2

end TransferSetup

section TransferSetup2

variable {Γ : Type u} [Group Γ] (H : Subgroup Γ)

/-- `X(t,γ) = t γ (rep (tγ))⁻¹`, which lies in `H`. -/
noncomputable def tfrX (t γ : Γ) : Γ := t * γ * (tfrRep H (t * γ))⁻¹

lemma tfrX_mem (t γ : Γ) : tfrX H t γ ∈ H := by
  have h := Quotient.out_eq (Quotient.mk'' (t * γ) : Quotient (QuotientGroup.rightRel H))
  have h2 : QuotientGroup.rightRel H (tfrRep H (t * γ)) (t * γ) := Quotient.exact h
  rw [QuotientGroup.rightRel_apply] at h2
  simpa [tfrX] using h2

/-- `X(t,γ)` as an element of `H`. -/
noncomputable def tfrKH (t γ : Γ) : H := ⟨tfrX H t γ, tfrX_mem H t γ⟩

@[simp] lemma tfrKH_coe (t γ : Γ) : (tfrKH H t γ : Γ) = tfrX H t γ := rfl

lemma tfrX_mul_rep (t γ : Γ) : tfrX H t γ * tfrRep H (t * γ) = t * γ := by
  simp [tfrX, mul_assoc]

lemma tfrX_mul (a σ τ : Γ) :
    tfrX H a σ * tfrX H (tfrRep H (a * σ)) τ = tfrX H a (σ * τ) := by
  have h1 : tfrRep H (tfrRep H (a * σ) * τ) = tfrRep H (a * (σ * τ)) := by
    rw [tfrRep_mul_right]
    congr 1
    group
  simp only [tfrX]
  rw [h1]
  group

lemma tfrKH_mul (a σ τ : Γ) :
    tfrKH H a σ * tfrKH H (tfrRep H (a * σ)) τ = tfrKH H a (σ * τ) := by
  apply Subtype.ext
  simp [tfrX_mul]

end TransferSetup2

section TransferShift

variable {Γ : Type u} [Group Γ] (H : Subgroup Γ)

/-- The "shift by `σ`" bijection of the right-coset space. -/
noncomputable def tfrShift (σ : Γ) :
    Quotient (QuotientGroup.rightRel H) → Quotient (QuotientGroup.rightRel H) :=
  fun c => Quotient.mk'' (Quotient.out c * σ)

lemma tfr_mk_mul_right {a b : Γ}
    (h : (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) = Quotient.mk'' b) (γ : Γ) :
    (Quotient.mk'' (a * γ) : Quotient (QuotientGroup.rightRel H)) = Quotient.mk'' (b * γ) := by
  rw [Quotient.eq'']
  rw [QuotientGroup.rightRel_apply]
  have h' : QuotientGroup.rightRel H a b := Quotient.exact h
  rw [QuotientGroup.rightRel_apply] at h'
  have hh : (b * γ) * (a * γ)⁻¹ = b * a⁻¹ := by group
  rw [hh]
  exact h'

lemma tfrShift_shift (σ : Γ) (c : Quotient (QuotientGroup.rightRel H)) :
    tfrShift H σ⁻¹ (tfrShift H σ c) = c := by
  simp only [tfrShift]
  rw [tfr_mk_mul_right H (Quotient.out_eq (Quotient.mk'' (Quotient.out c * σ))) σ⁻¹]
  rw [show (Quotient.out c * σ) * σ⁻¹ = Quotient.out c from by group]
  exact Quotient.out_eq c

/-- The permutation of the coset space induced by right multiplication by `σ`. -/
noncomputable def tfrShiftEquiv (σ : Γ) :
    Quotient (QuotientGroup.rightRel H) ≃ Quotient (QuotientGroup.rightRel H) where
  toFun := tfrShift H σ
  invFun := tfrShift H σ⁻¹
  left_inv c := tfrShift_shift H σ c
  right_inv c := by simpa using tfrShift_shift H σ⁻¹ c

variable [Fintype Γ]

noncomputable instance tfrQuotientFintype :
    Fintype (Quotient (QuotientGroup.rightRel H)) :=
  Fintype.ofSurjective (fun γ : Γ => (Quotient.mk'' γ : Quotient (QuotientGroup.rightRel H)))
    (fun q => Quotient.inductionOn q fun γ => ⟨γ, rfl⟩)

lemma tfrSum_shift (σ : Γ) {M : Type u} [AddCommMonoid M]
    (F : Quotient (QuotientGroup.rightRel H) → M) :
    (∑ c, F (tfrShift H σ c)) = ∑ c, F c :=
  Equiv.sum_comp (tfrShiftEquiv H σ) F

lemma tfr_card_eq_index : Fintype.card (Quotient (QuotientGroup.rightRel H)) = Subgroup.index H := by
  rw [Fintype.card_eq_nat_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H),
    ← Subgroup.index_eq_card H]

end TransferShift


section TransferCore

variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Fintype Γ]

/-- The 1-coboundary differential with trivial coefficients. -/
def tfrCob {M : Type u} [AddCommGroup M] (b : Γ → M) (σ τ : Γ) : M := b τ - b (σ * τ) + b σ

/-- The 2-cocycle differential with trivial coefficients. -/
def tfrCoc {M : Type u} [AddCommGroup M] (z : Γ → Γ → M) (σ τ υ : Γ) : M :=
  z τ υ - z (σ * τ) υ + z σ (τ * υ) - z σ τ

/-- Corestriction of a 1-cochain along `H ≤ Γ` (cochain level). -/
noncomputable def tfrCor1 {M : Type u} [AddCommGroup M] (w : H → M) (σ : Γ) : M :=
  ∑ c : Quotient (QuotientGroup.rightRel H), w (tfrKH H (Quotient.out c) σ)

/-- Corestriction of a 2-cochain along `H ≤ Γ` (cochain level). -/
noncomputable def tfrCor2 {M : Type u} [AddCommGroup M] (v : H → H → M) (σ τ : Γ) : M :=
  ∑ c : Quotient (QuotientGroup.rightRel H),
    v (tfrKH H (Quotient.out c) σ) (tfrKH H (tfrRep H (Quotient.out c * σ)) τ)

/-- Auxiliary cochain `P` of the transfer computation. -/
noncomputable def tfrP {M : Type u} [AddCommGroup M] (z : Γ → Γ → M) (γ : Γ) : M :=
  ∑ c : Quotient (QuotientGroup.rightRel H), z (Quotient.out c) γ

/-- Auxiliary cochain `Ξ` of the transfer computation. -/
noncomputable def tfrXi {M : Type u} [AddCommGroup M] (z : Γ → Γ → M) (γ : Γ) : M :=
  ∑ c : Quotient (QuotientGroup.rightRel H),
    z (tfrX H (Quotient.out c) γ) (tfrRep H (Quotient.out c * γ))

variable {M : Type u} [AddCommGroup M]

/-- The transfer commutes with the differential in degrees `1,2`. -/
lemma tfrCob_cor1 (w : H → M) (σ τ : Γ) :
    tfrCob (tfrCor1 H w) σ τ = tfrCor2 H (fun x y : H => tfrCob w x y) σ τ := by
  have hA : (∑ c : Quotient (QuotientGroup.rightRel H),
        w (tfrKH H (tfrRep H (Quotient.out c * σ)) τ))
      = ∑ c : Quotient (QuotientGroup.rightRel H), w (tfrKH H (Quotient.out c) τ) :=
    tfrSum_shift H σ (fun c => w (tfrKH H (Quotient.out c) τ))
  have hB : (∑ c : Quotient (QuotientGroup.rightRel H),
        w (tfrKH H (Quotient.out c) σ * tfrKH H (tfrRep H (Quotient.out c * σ)) τ))
      = ∑ c : Quotient (QuotientGroup.rightRel H), w (tfrKH H (Quotient.out c) (σ * τ)) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [tfrKH_mul]
  have hRHS : tfrCor2 H (fun x y : H => tfrCob w x y) σ τ
      = (∑ c : Quotient (QuotientGroup.rightRel H),
            w (tfrKH H (tfrRep H (Quotient.out c * σ)) τ))
        - (∑ c : Quotient (QuotientGroup.rightRel H),
            w (tfrKH H (Quotient.out c) σ * tfrKH H (tfrRep H (Quotient.out c * σ)) τ))
        + (∑ c : Quotient (QuotientGroup.rightRel H), w (tfrKH H (Quotient.out c) σ)) := by
    simp only [tfrCor2, tfrCob]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [tfrCob, tfrCor1, hRHS, hA, hB]
  abel

/-- Rearrangement helper: from `A - B + C - D = 0` conclude `A - B + C = D`. -/
lemma tfr_solve {A B C D : M} (h : A - B + C - D = 0) : A - B + C = D := sub_eq_zero.mp h

/-- Rearrangement helper: from `A - B + C - D = 0` conclude `C = D - A + B`. -/
lemma tfr_solve3 {A B C D : M} (h : A - B + C - D = 0) : C = D - A + B := by
  have h' : A - B + C = D := tfr_solve h
  rw [← h']
  abel

/-- Rearrangement helper: from `A - B + C - D = 0` conclude `B = A + C - D`. -/
lemma tfr_solve2 {A B C D : M} (h : A - B + C - D = 0) : B = A + C - D := by
  have h' : A + C = D + B := by
    have h2 : A - B + C = D := tfr_solve h
    rw [← h2]
    abel
  rw [eq_sub_iff_add_eq, add_comm B D, h']

/-- **The key identity.** For a 2-cocycle `z` on `Γ`, the transfer of the restriction of `z` to
`H` differs from `|H\Γ| • z` by an explicit coboundary. -/
lemma tfrCor2_res (z : Γ → Γ → M) (hz : ∀ σ τ υ : Γ, tfrCoc z σ τ υ = 0) (σ τ : Γ) :
    tfrCor2 H (fun x y : H => z x y) σ τ
      = (Fintype.card (Quotient (QuotientGroup.rightRel H))) • z σ τ
        + tfrCob (fun γ => tfrXi H z γ - tfrP H z γ) σ τ := by
  have hper : ∀ c : Quotient (QuotientGroup.rightRel H),
      z (tfrX H (Quotient.out c) σ) (tfrX H (tfrRep H (Quotient.out c * σ)) τ)
        = z (tfrX H (tfrRep H (Quotient.out c * σ)) τ) (tfrRep H (Quotient.out c * (σ * τ)))
          - z (tfrX H (Quotient.out c) (σ * τ)) (tfrRep H (Quotient.out c * (σ * τ)))
          + z (tfrX H (Quotient.out c) σ) (tfrRep H (Quotient.out c * σ) * τ) := by
    intro c
    have h1 : tfrX H (Quotient.out c) σ * tfrX H (tfrRep H (Quotient.out c * σ)) τ
        = tfrX H (Quotient.out c) (σ * τ) := tfrX_mul H (Quotient.out c) σ τ
    have h2 : tfrRep H (tfrRep H (Quotient.out c * σ) * τ)
        = tfrRep H (Quotient.out c * (σ * τ)) := by
      rw [tfrRep_mul_right]
      congr 1
      group
    have h3 : tfrX H (tfrRep H (Quotient.out c * σ)) τ * tfrRep H (Quotient.out c * (σ * τ))
        = tfrRep H (Quotient.out c * σ) * τ := by
      rw [← h2, tfrX_mul_rep]
    have key := hz (tfrX H (Quotient.out c) σ) (tfrX H (tfrRep H (Quotient.out c * σ)) τ)
      (tfrRep H (Quotient.out c * (σ * τ)))
    simp only [tfrCoc] at key
    rw [h1, h3] at key
    exact (tfr_solve key).symm
  have hsum : tfrCor2 H (fun x y : H => z x y) σ τ
      = (∑ c : Quotient (QuotientGroup.rightRel H),
            z (tfrX H (tfrRep H (Quotient.out c * σ)) τ) (tfrRep H (Quotient.out c * (σ * τ))))
        - (∑ c : Quotient (QuotientGroup.rightRel H),
            z (tfrX H (Quotient.out c) (σ * τ)) (tfrRep H (Quotient.out c * (σ * τ))))
        + (∑ c : Quotient (QuotientGroup.rightRel H),
            z (tfrX H (Quotient.out c) σ) (tfrRep H (Quotient.out c * σ) * τ)) := by
    have hcong : (∑ c : Quotient (QuotientGroup.rightRel H),
        z (tfrX H (Quotient.out c) σ) (tfrX H (tfrRep H (Quotient.out c * σ)) τ))
        = ∑ c : Quotient (QuotientGroup.rightRel H),
          (z (tfrX H (tfrRep H (Quotient.out c * σ)) τ) (tfrRep H (Quotient.out c * (σ * τ)))
            - z (tfrX H (Quotient.out c) (σ * τ)) (tfrRep H (Quotient.out c * (σ * τ)))
            + z (tfrX H (Quotient.out c) σ) (tfrRep H (Quotient.out c * σ) * τ)) :=
      Finset.sum_congr rfl (fun c _ => hper c)
    simp only [tfrCor2, tfrKH_coe]
    rw [hcong, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs1 : (∑ c : Quotient (QuotientGroup.rightRel H),
        z (tfrX H (tfrRep H (Quotient.out c * σ)) τ)
          (tfrRep H (Quotient.out c * (σ * τ)))) = tfrXi H z τ := by
    rw [tfrXi, ← tfrSum_shift H σ
      (fun c => z (tfrX H (Quotient.out c) τ) (tfrRep H (Quotient.out c * τ)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h2 : tfrRep H (tfrRep H (Quotient.out c * σ) * τ)
        = tfrRep H (Quotient.out c * (σ * τ)) := by
      rw [tfrRep_mul_right]
      congr 1
      group
    show z (tfrX H (tfrRep H (Quotient.out c * σ)) τ) (tfrRep H (Quotient.out c * (σ * τ)))
      = z (tfrX H (tfrRep H (Quotient.out c * σ)) τ)
          (tfrRep H (tfrRep H (Quotient.out c * σ) * τ))
    rw [h2]
  have hs2 : (∑ c : Quotient (QuotientGroup.rightRel H),
        z (tfrX H (Quotient.out c) (σ * τ)) (tfrRep H (Quotient.out c * (σ * τ))))
      = tfrXi H z (σ * τ) := rfl
  have hB3 : (∑ c : Quotient (QuotientGroup.rightRel H),
      z (tfrRep H (Quotient.out c * σ)) τ) = tfrP H z τ := by
    rw [tfrP, ← tfrSum_shift H σ (fun c => z (Quotient.out c) τ)]
    exact Finset.sum_congr rfl (fun c _ => rfl)
  have hper4 : ∀ c : Quotient (QuotientGroup.rightRel H),
      z (Quotient.out c * σ) τ = z σ τ + z (Quotient.out c) (σ * τ) - z (Quotient.out c) σ := by
    intro c
    have key := hz (Quotient.out c) σ τ
    simp only [tfrCoc] at key
    exact tfr_solve2 key
  have hC3 : (∑ c : Quotient (QuotientGroup.rightRel H), z (Quotient.out c * σ) τ)
      = (Fintype.card (Quotient (QuotientGroup.rightRel H))) • z σ τ
        + tfrP H z (σ * τ) - tfrP H z σ := by
    rw [Finset.sum_congr rfl (fun c _ => hper4 c)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.card_univ]
    rfl
  have hper3 : ∀ c : Quotient (QuotientGroup.rightRel H),
      z (tfrX H (Quotient.out c) σ) (tfrRep H (Quotient.out c * σ) * τ)
        = z (tfrX H (Quotient.out c) σ) (tfrRep H (Quotient.out c * σ))
          - z (tfrRep H (Quotient.out c * σ)) τ
          + z (Quotient.out c * σ) τ := by
    intro c
    have h1 : tfrX H (Quotient.out c) σ * tfrRep H (Quotient.out c * σ)
        = Quotient.out c * σ := tfrX_mul_rep H (Quotient.out c) σ
    have key := hz (tfrX H (Quotient.out c) σ) (tfrRep H (Quotient.out c * σ)) τ
    simp only [tfrCoc] at key
    rw [h1] at key
    exact tfr_solve3 key
  have hs3 : (∑ c : Quotient (QuotientGroup.rightRel H),
        z (tfrX H (Quotient.out c) σ) (tfrRep H (Quotient.out c * σ) * τ))
      = tfrXi H z σ - tfrP H z τ
        + ((Fintype.card (Quotient (QuotientGroup.rightRel H))) • z σ τ
            + tfrP H z (σ * τ) - tfrP H z σ) := by
    rw [Finset.sum_congr rfl (fun c _ => hper3 c)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hB3, hC3]
    rfl
  rw [hsum, hs1, hs2, hs3, tfrCob]
  abel

end TransferCore

section TransferExists

variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Fintype Γ]
variable {M : Type u} [AddCommGroup M]

/-- **Cochain-level transfer.** If a `2`-cocycle `z` on `Γ` becomes a coboundary on the subgroup
`H`, then `[Γ : H] • z` is a coboundary on `Γ`. -/
lemma tfr_exists_smul_cob (z : Γ → Γ → M) (hz : ∀ σ τ υ : Γ, tfrCoc z σ τ υ = 0)
    (b : H → M) (hb : ∀ x y : H, z (x : Γ) (y : Γ) = tfrCob b x y) :
    ∃ B : Γ → M, ∀ σ τ : Γ, tfrCob B σ τ
      = (Fintype.card (Quotient (QuotientGroup.rightRel H))) • z σ τ := by
  refine ⟨fun γ => tfrCor1 H b γ - tfrXi H z γ + tfrP H z γ, fun σ τ => ?_⟩
  have h1 : tfrCob (tfrCor1 H b) σ τ = tfrCor2 H (fun x y : H => tfrCob b x y) σ τ :=
    tfrCob_cor1 H b σ τ
  have h2 : tfrCor2 H (fun x y : H => tfrCob b x y) σ τ
      = tfrCor2 H (fun x y : H => z x y) σ τ := by
    simp only [tfrCor2, tfrKH_coe]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (hb _ _).symm
  have h3 := tfrCor2_res H z hz σ τ
  have h4 : tfrCob (fun γ => tfrCor1 H b γ - tfrXi H z γ + tfrP H z γ) σ τ
      = tfrCob (tfrCor1 H b) σ τ - tfrCob (fun γ => tfrXi H z γ - tfrP H z γ) σ τ := by
    simp only [tfrCob]
    abel
  rw [h4, h1, h2, h3]
  abel

end TransferExists

section LevelProof

variable {p : ℕ} {Γ : Type u} [Group Γ] [Fintype Γ] (H : Subgroup Γ)

omit [Fintype Γ] in
/-- The cochain differential of the transfer agrees with the Mathlib differential for the trivial
representation. -/
lemma tfrCob_eq_d₁₂ (B : Γ → Coeff.{u} p) (σ τ : Γ) :
    tfrCob B σ τ
      = (groupCohomology.d₁₂ (Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p))).hom B (σ, τ) := by
  rw [groupCohomology.d₁₂_hom_apply, Rep.trivial_ρ, LinearMap.id_apply, tfrCob]

omit [Fintype Γ] in
/-- The `2`-cocycle differential of the transfer agrees with the Mathlib differential for the
trivial representation. -/
lemma tfrCoc_eq_d₂₃ (w : Γ × Γ → Coeff.{u} p) (σ τ υ : Γ) :
    tfrCoc (fun a b => w (a, b)) σ τ υ
      = (groupCohomology.d₂₃ (Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p))).hom w (σ, τ, υ) := by
  rw [groupCohomology.d₂₃_hom_apply, Rep.trivial_ρ, LinearMap.id_apply, tfrCoc]

omit [Fintype Γ] in
/-- The map on `2`-cocycles induced by the inclusion of a subgroup, on explicit cochains. -/
lemma mapCocycles₂_subtype_apply
    (w : groupCohomology.cocycles₂ (Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p))) (x y : H) :
    ((groupCohomology.mapCocycles₂ H.subtype (NK.BrauerHasse.trivHom H.subtype)) w) (x, y)
      = w ((x : Γ), (y : Γ)) := by
  rw [groupCohomology.coe_mapCocycles₂]
  have h : (groupCohomology.cochainsMap₂ H.subtype (NK.BrauerHasse.trivHom H.subtype)) ⇑w
      = fun q : H × H => w ((q.1 : Γ), (q.2 : Γ)) := by
    funext q
    obtain ⟨a, b⟩ := q
    simp only [groupCohomology.cochainsMap₂, LinearMap.comp_apply, LinearMap.compLeft_apply,
      LinearMap.funLeft_apply, Prod.map_apply, Function.comp_apply, ModuleCat.hom_ofHom]
    rfl
  rw [h]

/-- **Subgroup form of the theorem.** Restriction to a subgroup of prime-to-`p` index is injective
on `H²(·, Z/p)`. -/
theorem H2_map_subtype_injective (hp : Nat.Coprime (Subgroup.index H) p) :
    Function.Injective (fun x : NK.BrauerHasse.H2 p Γ =>
      (NK.BrauerHasse.H2.map (p := p) H.subtype).hom x) := by
  suffices hker : ∀ x : NK.BrauerHasse.H2 p Γ,
      (NK.BrauerHasse.H2.map (p := p) H.subtype).hom x = 0 → x = 0 by
    intro x y hxy
    have hxy' : (NK.BrauerHasse.H2.map (p := p) H.subtype).hom x
        = (NK.BrauerHasse.H2.map (p := p) H.subtype).hom y := hxy
    have h1 : (NK.BrauerHasse.H2.map (p := p) H.subtype).hom (x - y) = 0 := by
      rw [map_sub, hxy', sub_self]
    exact sub_eq_zero.mp (hker (x - y) h1)
  intro x hx
  revert hx
  refine groupCohomology.H2_induction_on (A := Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p)) x ?_
  intro w hx
  have hx2 : (groupCohomology.H2π (Rep.trivial (Coeff.{u} p) ↥H (Coeff.{u} p)))
      ((groupCohomology.mapCocycles₂ H.subtype (NK.BrauerHasse.trivHom H.subtype)) w) = 0 := by
    rw [← groupCohomology.H2π_comp_map_apply H.subtype (NK.BrauerHasse.trivHom H.subtype) w]
    exact hx
  obtain ⟨β, hβ⟩ := LinearMap.mem_range.mp
    ((groupCohomology.H2π_eq_zero_iff (A := Rep.trivial (Coeff.{u} p) ↥H (Coeff.{u} p)) _).mp hx2)
  have hb : ∀ x y : H, w ((x : Γ), (y : Γ)) = tfrCob β x y := by
    intro x y
    have h1 := congrFun hβ (x, y)
    rw [mapCocycles₂_subtype_apply H w x y, ← tfrCob_eq_d₁₂ β x y] at h1
    exact h1.symm
  have hw : ∀ σ τ υ : Γ, tfrCoc (fun a b => w (a, b)) σ τ υ = 0 := by
    intro σ τ υ
    have h2 : (groupCohomology.d₂₃ (Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p))).hom (⇑w)
        (σ, τ, υ) = 0 := congrFun w.2 (σ, τ, υ)
    rw [tfrCoc_eq_d₂₃ (⇑w) σ τ υ]
    exact h2
  obtain ⟨B₀, hB₀⟩ := tfr_exists_smul_cob H (fun a b => w (a, b)) hw β hb
  have hmem : ⇑((Fintype.card (Quotient (QuotientGroup.rightRel H)) : ℕ) • w)
      ∈ groupCohomology.coboundaries₂ (Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p)) := by
    refine LinearMap.mem_range.mpr ⟨B₀, ?_⟩
    funext q
    obtain ⟨σ, τ⟩ := q
    rw [← tfrCob_eq_d₁₂ B₀ σ τ]
    show tfrCob B₀ σ τ
      = (Fintype.card (Quotient (QuotientGroup.rightRel H))) • (w (σ, τ))
    exact hB₀ σ τ
  have hzero : (groupCohomology.H2π (Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p)))
      ((Fintype.card (Quotient (QuotientGroup.rightRel H)) : ℕ) • w) = 0 :=
    (groupCohomology.H2π_eq_zero_iff _).mpr hmem
  have hsmul : (Fintype.card (Quotient (QuotientGroup.rightRel H)) : ℕ)
      • ((groupCohomology.H2π (Rep.trivial (Coeff.{u} p) Γ (Coeff.{u} p))) w) = 0 := by
    rw [← map_nsmul]
    exact hzero
  rw [← Nat.cast_smul_eq_nsmul (Coeff.{u} p)] at hsmul
  have hcop : Nat.Coprime (Fintype.card (Quotient (QuotientGroup.rightRel H))) p := by
    rw [tfr_card_eq_index H]
    exact hp
  have hunit : IsUnit ((Fintype.card (Quotient (QuotientGroup.rightRel H)) : Coeff.{u} p)) := by
    have h1 : IsUnit ((Fintype.card (Quotient (QuotientGroup.rightRel H)) : ZMod p)) :=
      (ZMod.isUnit_iff_coprime _ p).mpr hcop
    have h2 := IsUnit.map (ULift.ringEquiv.symm : ZMod p ≃+* Coeff.{u} p) h1
    simpa using h2
  exact (IsUnit.smul_eq_zero hunit).mp hsmul

end LevelProof

section MainTheorem

variable {p : ℕ} {G K : Type u} [Group G] [Group K]

/-- `H².map` of a bijective group homomorphism is injective. -/
lemma H2_map_injective_of_bijective (g : G →* K) (hg : Function.Bijective g) :
    Function.Injective (fun x : H2 p K => (H2.map (p := p) g).hom x) := by
  intro x y hxy
  set g' : K ≃* G := (MulEquiv.ofBijective g hg).symm with hg'def
  have hgk : g.comp (g' : K →* G) = MonoidHom.id K := by
    ext z
    simpa [hg'def, MulEquiv.ofBijective_apply] using
      MulEquiv.apply_symm_apply (MulEquiv.ofBijective g hg) z
  have hgh : (H2.map (p := p) (g.comp (g' : K →* G))).hom
      = (H2.map (p := p) (g' : K →* G)).hom ∘ (H2.map (p := p) g).hom := by
    rw [H2.map_comp, ModuleCat.hom_comp]
    rfl
  have key : ∀ z : H2 p K,
      (H2.map (p := p) (g' : K →* G)).hom ((H2.map (p := p) g).hom z) = z := by
    intro z
    have h2 : (H2.map (p := p) (g.comp (g' : K →* G))).hom z
        = (H2.map (p := p) (MonoidHom.id K)).hom z := by
      rw [hgk, H2.map_id]
    rw [hgh] at h2
    simpa using h2
  have hxy' : (H2.map (p := p) g).hom x = (H2.map (p := p) g).hom y := hxy
  calc x = (H2.map (p := p) (g' : K →* G)).hom ((H2.map (p := p) g).hom x) := (key x).symm
    _ = (H2.map (p := p) (g' : K →* G)).hom ((H2.map (p := p) g).hom y) := by rw [hxy']
    _ = y := key y

end MainTheorem

section FinalTheorem

/-- **Restriction is injective on `H²(·, Z/p)` for subgroups of prime-to-`p` index.**

For an injective group homomorphism `f : Δ →* Γ` of finite groups whose index `[Γ : f(Δ)]` is
coprime to `p`, the induced map `NK.BrauerHasse.H2.map f : H²(Γ, Z/p) → H²(Δ, Z/p)` — i.e. the
restriction to a subgroup of index prime to `p` — is injective.

This is the transfer (corestriction) argument specialised to the trivial coefficients `Z/p`:
`cor ∘ res = [Γ : f(Δ)]` on `H²(Γ, Z/p)`, the module `H²(Γ, Z/p)` is `p`-torsion (it is a
`Z/p`-module), and multiplication by an integer coprime to `p` is injective on a `p`-torsion group.
An alternative elementary route for finite groups is to average a `1`-cochain over a set of coset
representatives of `f(Δ)` in `Γ`, the index being invertible modulo `p`.

This is the group-theoretic form of the level-wise statement that the localisation at a place `A`
is injective on the level `L` whenever the decomposition subgroup
`(U ⊓ stabSubgroup A)/((U ⊓ stabSubgroup A) ⊓ Gal(K'/L))` has index prime to `p` in
`U/(U ⊓ Gal(K'/L))`. -/
theorem H2_map_injective_of_coprime_index (p : ℕ) {Δ Γ : Type u} [Group Δ] [Group Γ] [Finite Γ]
    (f : Δ →* Γ) (hf : Function.Injective f)
    (h : Nat.Coprime (Subgroup.index (MonoidHom.range f)) p) :
    Function.Injective (fun x : NK.BrauerHasse.H2 p Γ =>
      (NK.BrauerHasse.H2.map (p := p) f).hom x) := by
  letI : Fintype Γ := Fintype.ofFinite Γ
  intro x y hxy
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨fun a b hab => hf (Subtype.ext_iff.mp hab), f.rangeRestrict_surjective⟩
  have hcomp : (NK.BrauerHasse.H2.map (p := p) f).hom
      = (NK.BrauerHasse.H2.map (p := p) f.rangeRestrict).hom
        ∘ (NK.BrauerHasse.H2.map (p := p) (MonoidHom.range f).subtype).hom := by
    rw [← MonoidHom.subtype_comp_rangeRestrict f, NK.BrauerHasse.H2.map_comp,
      ModuleCat.hom_comp]
    rfl
  have hxy' : (NK.BrauerHasse.H2.map (p := p) f).hom x
      = (NK.BrauerHasse.H2.map (p := p) f).hom y := hxy
  rw [hcomp] at hxy'
  simp only [Function.comp_apply] at hxy'
  exact H2_map_subtype_injective (p := p) (MonoidHom.range f) h
    (H2_map_injective_of_bijective (p := p) f.rangeRestrict hbij hxy')

end FinalTheorem

end NK.HassePrinciple
