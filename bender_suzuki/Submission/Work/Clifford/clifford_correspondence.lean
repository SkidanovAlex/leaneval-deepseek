import Mathlib
import Submission.Work.Clifford.clifford_decomposition
import Submission.Work.Clifford.clifford_induction_mem_Irr
import Submission.Work.Clifford.exists_irr_constituent_resFun
import Submission.Work.Clifford.cfInner_indFun
import Submission.Work.Clifford.cfInner_indFun_normal
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.nat_sum_sq_eq_imp_eq
import Submission.Work.Clifford.inertia_subgroupOf_eq_top
import Submission.Work.Induction.indFun_trans
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.Basic
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.CharCore.cfInner_character_nat
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.mem_Irr_iff_fdrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.clifford_correspondence`

**The Clifford correspondence.**  Let `N` be a normal subgroup of a finite group `G`, let
`θ ∈ Irr N` be an irreducible character of `N` with inertia group `I = I_G(θ)`, and let
`χ ∈ Irr G` be an irreducible character of `G` lying over `θ` (that is, `θ` occurs in the
restriction `χ|_N`).  Then there is a **unique** irreducible character `ψ` of `I` which lies
over `θ` and induces to `χ`:

`Ind_I^G ψ = χ`.

## Proof

Write `I = I_G(θ)`, let `θ_I` be the pullback of `θ` to `N.subgroupOf I` (it is `I`-invariant),
and put `α = Ind_N^G θ`, `β = Ind_{N.subgroupOf I}^I θ_I`, so that `α = Ind_I^G β`
(transitivity of induction).  Let

* `E χ = ⟪α, χ⟫_G` for `χ ∈ Irr G`,
* `F ψ = ⟪β, ψ⟫_I` for `ψ ∈ Irr I`,
* `a χ ψ = ⟪Ind_I^G ψ, χ⟫_G`,

all of which are natural numbers (Frobenius reciprocity and the fact that the multiplicity of
an irreducible character in a character is a natural number).  Then

* (Parseval) `⟪α, α⟫_G = ∑_χ (E χ)^2` and `⟪β, β⟫_I = ∑_ψ (F ψ)^2`;
* (norm of an induced character) both sides equal `|I| / |N|`, so `∑_χ (E χ)^2 = ∑_ψ (F ψ)^2`;
* (Frobenius reciprocity) `E χ = ∑_ψ a χ ψ * F ψ`.

The Clifford correspondence rests on the induction half (`clifford_induction_mem_Irr`): for
`ψ ∈ Irr I` lying over `θ`, the character `Ind_I^G ψ` is irreducible.  Consequently
`a χ ψ = 1` if `Ind_I^G ψ = χ` and `a χ ψ = 0` otherwise, so that

`E χ = ∑_{ψ : Ind_I^G ψ = χ} F ψ`.

Every `ψ ∈ Irr I` with `F ψ ≠ 0` lies over `θ` (`LiesOver N I _ θ ψ ↔ F ψ ≠ 0`, via the
identification of `⟪Ind_{N.subgroupOf I}^I θ_I, ψ⟫` with `⟪ψ|_N, θ⟫` along the group
isomorphism `N.subgroupOf I ≃* N`), hence occurs in exactly one fibre.  Summing the displayed
identity and comparing with `∑_ψ (F ψ)^2` shows that each fibre contains at most one `ψ`
(Cauchy–Schwarz for natural numbers: `(∑ f)^2 = ∑ f^2` forces at most one non-zero summand),
while `E χ ≠ 0` for our `χ` (it is the conjugate of `⟪χ|_N, θ⟫ ≠ 0`) shows that its fibre is
non-empty.  This gives existence and uniqueness of `ψ`.
-/

noncomputable section

open Classical

namespace Work.Clifford

universe u

theorem corr_mem_Irr_charCore {G : Type u} [Group G] [Fintype G] {χ : G → ℂ} :
    χ ∈ Irr G ↔ χ ∈ Work.CharCore.Irr G := by
  rw [mem_Irr]
  exact (Work.CharCore.mem_Irr_iff_fdrep χ).symm

theorem corr_cfInner_eq_charCore {G : Type u} [Group G] [Fintype G] (f g : G → ℂ) :
    cfInner f g = Work.CharCore.cfInner f g := rfl

theorem corr_isClassFun_indFun {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ) :
    IsClassFun (indFun H φ) :=
  Work.Induction.isClassFun_indFun H φ

theorem corr_indFun_trans {G : Type u} [Group G] [Fintype G] {K H : Subgroup G} (hKH : K ≤ H)
    (φ : K → ℂ) :
    indFun H (indFun (K.subgroupOf H) (fun x => φ (Subgroup.subgroupOfEquivOfLe hKH x))) =
      indFun K φ :=
  Work.Induction.indFun_trans hKH φ

theorem corr_indFun_sum {G : Type u} [Group G] [Fintype G] {ι : Type u} (H : Subgroup G)
    (s : Finset ι) (F : ι → H → ℂ) :
    indFun H (∑ i ∈ s, F i) = ∑ i ∈ s, indFun H (F i) :=
  Work.Induction.indFun_sum H s F

theorem corr_indFun_smul {G : Type u} [Group G] [Fintype G] (H : Subgroup G) (c : ℂ)
    (φ : H → ℂ) : indFun H (c • φ) = c • indFun H φ :=
  Work.Induction.indFun_smul H c φ

theorem corr_classFun_eq_sum_irr {G : Type u} [Group G] [Fintype G] {F : G → ℂ}
    (hF : IsClassFun F) :
    F = ∑ χ : ↥(Work.CharCore.Irr G), cfInner F (χ : G → ℂ) • (χ : G → ℂ) := by
  conv_lhs => rw [Work.CharCore.classFun_eq_sum_irr hF]
  rw [Finset.sum_subtype (s := Work.CharCore.Irr G) (p := fun x => x ∈ Work.CharCore.Irr G)
    (fun x => Iff.rfl) (f := fun χ => Work.CharCore.cfInner F χ • χ)]
  exact Finset.sum_congr rfl fun χ _ => by rw [corr_cfInner_eq_charCore]

theorem corr_cfInner_comp_mulEquiv {H K : Type u} [Group H] [Fintype H] [Group K] [Fintype K]
    (e : H ≃* K) (f g : K → ℂ) :
    cfInner (fun h => f (e h)) (fun h => g (e h)) = cfInner f g := by
  have hcard : Fintype.card H = Fintype.card K := Fintype.card_congr e.toEquiv
  rw [cfInner, cfInner, hcard]
  congr 1
  exact Fintype.sum_equiv e.toEquiv _ _ (fun h => rfl)

theorem corr_cfInner_inst {G : Type u} [Group G] (i₁ i₂ : Fintype G) (f g : G → ℂ) :
    @cfInner G i₁ f g = @cfInner G i₂ f g := by
  have hcard : @Fintype.card G i₁ = @Fintype.card G i₂ := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  have huniv : (@Finset.univ G i₁) = (@Finset.univ G i₂) := Finset.ext fun x => by simp
  unfold cfInner
  rw [hcard, huniv]

theorem corr_isConstituentOf_inst {H : Type u} [Group H] (i₁ i₂ : Fintype H)
    (θ f : H → ℂ) :
    @IsConstituentOf H _ i₁ θ f ↔ @IsConstituentOf H _ i₂ θ f := by
  unfold IsConstituentOf
  rw [corr_cfInner_inst i₁ i₂ f θ]

/-- `LiesOver` is "`θ` is a constituent of the restriction of `ψ`", phrased with the Fintype
instance that is explicitly in scope (the definition of `LiesOver` uses a synthesized one). -/
theorem corr_liesOver_iff {G : Type u} [Group G] [Fintype G] {N T : Subgroup G} [Fintype N]
    (h : N ≤ T) (θ : N → ℂ) (ψ : T → ℂ) :
    LiesOver N T h θ ψ ↔ IsConstituentOf θ (resFunOfLe h ψ) := by
  unfold LiesOver
  exact corr_isConstituentOf_inst _ _ θ (resFunOfLe h ψ)

theorem corr_cfInner_self_eq_sum_sq {G : Type u} [Group G] [Fintype G] {F : G → ℂ}
    (hF : IsClassFun F) (n : ↥(Work.CharCore.Irr G) → ℕ)
    (hn : ∀ χ : ↥(Work.CharCore.Irr G), cfInner F (χ : G → ℂ) = (n χ : ℂ)) :
    cfInner F F = ∑ χ : ↥(Work.CharCore.Irr G), ((n χ : ℂ)) ^ 2 := by
  have hF' : F = ∑ χ : ↥(Work.CharCore.Irr G), (n χ : ℂ) • (χ : G → ℂ) := by
    rw [corr_classFun_eq_sum_irr hF]
    exact Finset.sum_congr rfl fun χ _ => by rw [hn χ]
  rw [hF', cfInner_sum_smul_left]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [cfInner_sum_smul_right, Finset.sum_eq_single χ]
  · rw [cfInner_eq_ite_of_mem_Irr ((corr_mem_Irr_charCore).mpr χ.2) ((corr_mem_Irr_charCore).mpr χ.2)]
    simp [sq]
  · intro b _ hb
    rw [cfInner_eq_ite_of_mem_Irr ((corr_mem_Irr_charCore).mpr χ.2) ((corr_mem_Irr_charCore).mpr b.2)]
    have hne : ¬ ((χ : G → ℂ) = (b : G → ℂ)) := fun h => hb (Subtype.ext h).symm
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ χ) h

theorem corr_nat_mul_sum_sq_eq {ι : Type u} [Fintype ι] (n : ι → ℕ) {a b : ℕ} (hb : b ≠ 0)
    (h : ∑ i, ((n i : ℂ)) ^ 2 = (a : ℂ) * (b : ℂ)⁻¹) : b * ∑ i, (n i) ^ 2 = a := by
  have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hcast : ((b * ∑ i, (n i) ^ 2 : ℕ) : ℂ) = (a : ℂ) := by
    push_cast
    rw [h, ← mul_assoc, mul_comm (b : ℂ) (a : ℂ), mul_assoc, mul_inv_cancel₀ hb', mul_one]
  exact Nat.cast_injective (R := ℂ) hcast

theorem corr_nat_cfInner_indFun {G : Type u} [Group G] [Fintype G] {H : Subgroup G} [Fintype H]
    {θ : H → ℂ} (hθ : θ ∈ Work.CharCore.Irr H) {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) :
    ∃ n : ℕ, cfInner (indFun H θ) χ = (n : ℂ) := by
  obtain ⟨V, hV, hVχ⟩ := (Work.CharCore.mem_Irr_iff_fdrep χ).mp hχ
  let ρ : Representation ℂ H V := V.ρ.comp H.subtype
  have hρ : ρ.character = resFun H χ := by
    funext h
    show V.character (H.subtype h) = χ h
    rw [← hVχ]
    rfl
  obtain ⟨n, hn⟩ := Work.CharCore.cfInner_character_nat ρ hθ
  refine ⟨n, ?_⟩
  have h1 : cfInner (resFun H χ) θ = (n : ℂ) := by
    rw [corr_cfInner_eq_charCore, ← hρ, hn]
  rw [cfInner_indFun (H := H) θ (Work.CharCore.isClassFun_of_mem_Irr hχ), cfInner_conj_symm, h1]
  simp

theorem clifford_correspondence {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) {χ : G → ℂ}
    (hχ : χ ∈ Work.Clifford.Irr G) (h : Work.Clifford.IsConstituentOf θ (Work.Clifford.resFun N χ)) :
    ∃! ψ : (Work.Clifford.inertia N θ) → ℂ,
      ψ ∈ Work.Clifford.Irr (Work.Clifford.inertia N θ) ∧
        Work.Clifford.LiesOver N (Work.Clifford.inertia N θ)
          (Work.Clifford.le_inertia_of_mem_Irr hθ) θ ψ ∧
        Work.Clifford.indFun (Work.Clifford.inertia N θ) ψ = χ := by
  classical
  let I : Subgroup G := inertia N θ
  let hNI : N ≤ I := le_inertia_of_mem_Irr hθ
  let θI : ↥(N.subgroupOf I) → ℂ := fun x => θ (Subgroup.subgroupOfEquivOfLe hNI x)
  have hθI : θI ∈ Irr ↥(N.subgroupOf I) := Irr_comp_mulEquiv (Subgroup.subgroupOfEquivOfLe hNI) hθ
  have hθIC : θI ∈ Work.CharCore.Irr ↥(N.subgroupOf I) := (corr_mem_Irr_charCore).mp hθI
  have hθC : θ ∈ Work.CharCore.Irr ↥N := (corr_mem_Irr_charCore).mp hθ
  have hχC : χ ∈ Work.CharCore.Irr G := (corr_mem_Irr_charCore).mp hχ
  -- the inertia of `θI` inside `I` is everything
  have hI_top : inertia (N.subgroupOf I) θI = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_inertia]
    change conjFun (N.subgroupOf I) g (fun x => θ (Subgroup.subgroupOfEquivOfLe hNI x)) = θI
    rw [conjFun_subgroupOfEquivOfLe hNI g θ]
    refine funext fun x => ?_
    exact congrFun ((mem_inertia N θ (g : G)).mp g.2) (Subgroup.subgroupOfEquivOfLe hNI x)
  -- transitivity of induction
  have hαβ : indFun N θ = indFun I (indFun (N.subgroupOf I) θI) := by
    show indFun N θ = indFun I (indFun (N.subgroupOf I) (fun x => θ (Subgroup.subgroupOfEquivOfLe hNI x)))
    exact (corr_indFun_trans hNI θ).symm
  -- the multiplicities, as natural numbers
  have hEex : ∀ χ : ↥(Work.CharCore.Irr G), ∃ n : ℕ,
      cfInner (indFun N θ) (χ : G → ℂ) = (n : ℂ) :=
    fun χ => corr_nat_cfInner_indFun hθC χ.2
  let E : ↥(Work.CharCore.Irr G) → ℕ := fun χ => (hEex χ).choose
  have hE : ∀ χ : ↥(Work.CharCore.Irr G), cfInner (indFun N θ) (χ : G → ℂ) = (E χ : ℂ) :=
    fun χ => (hEex χ).choose_spec
  have hFex : ∀ ψ : ↥(Work.CharCore.Irr ↥I), ∃ n : ℕ,
      cfInner (indFun (N.subgroupOf I) θI) (ψ : ↥I → ℂ) = (n : ℂ) :=
    fun ψ => corr_nat_cfInner_indFun hθIC ψ.2
  let F : ↥(Work.CharCore.Irr ↥I) → ℕ := fun ψ => (hFex ψ).choose
  have hF : ∀ ψ : ↥(Work.CharCore.Irr ↥I),
      cfInner (indFun (N.subgroupOf I) θI) (ψ : ↥I → ℂ) = (F ψ : ℂ) :=
    fun ψ => (hFex ψ).choose_spec
  have haex : ∀ χ : ↥(Work.CharCore.Irr G), ∀ ψ : ↥(Work.CharCore.Irr ↥I), ∃ n : ℕ,
      cfInner (indFun I (ψ : ↥I → ℂ)) (χ : G → ℂ) = (n : ℂ) :=
    fun χ ψ => corr_nat_cfInner_indFun ψ.2 χ.2
  let a : ↥(Work.CharCore.Irr G) → ↥(Work.CharCore.Irr ↥I) → ℕ := fun χ ψ => (haex χ ψ).choose
  have ha : ∀ (χ : ↥(Work.CharCore.Irr G)) (ψ : ↥(Work.CharCore.Irr ↥I)),
      cfInner (indFun I (ψ : ↥I → ℂ)) (χ : G → ℂ) = (a χ ψ : ℂ) :=
    fun χ ψ => (haex χ ψ).choose_spec
  -- Parseval at both levels
  have hsumG : cfInner (indFun N θ) (indFun N θ)
      = ∑ χ : ↥(Work.CharCore.Irr G), ((E χ : ℂ)) ^ 2 :=
    corr_cfInner_self_eq_sum_sq (corr_isClassFun_indFun N θ) E hE
  have hsumI : cfInner (indFun (N.subgroupOf I) θI) (indFun (N.subgroupOf I) θI)
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I), ((F ψ : ℂ)) ^ 2 :=
    corr_cfInner_self_eq_sum_sq (corr_isClassFun_indFun (N.subgroupOf I) θI) F hF
  -- the norms
  have hnormα : cfInner (indFun N θ) (indFun N θ)
      = (Nat.card ↥I : ℂ) * (Nat.card ↥N : ℂ)⁻¹ :=
    cfInner_indFun_normal hθ
  have hnormβ : cfInner (indFun (N.subgroupOf I) θI) (indFun (N.subgroupOf I) θI)
      = (Nat.card ↥I : ℂ) * (Nat.card ↥N : ℂ)⁻¹ := by
    have h := cfInner_indFun_normal (N := N.subgroupOf I) hθI
    rw [hI_top] at h
    have hTop : Nat.card ↥(⊤ : Subgroup ↥I) = Nat.card ↥I :=
      Nat.card_congr (Subgroup.topEquiv (G := ↥I)).toEquiv
    have hCard : Nat.card ↥(N.subgroupOf I) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNI).toEquiv
    rw [hTop, hCard] at h
    exact h
  -- the norm identity
  have hsum_eq : ∑ χ : ↥(Work.CharCore.Irr G), (E χ) ^ 2
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I), (F ψ) ^ 2 := by
    have hNne : Nat.card ↥N ≠ 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_ne_zero
    have h1 : Nat.card ↥N * ∑ χ : ↥(Work.CharCore.Irr G), (E χ) ^ 2 = Nat.card ↥I :=
      corr_nat_mul_sum_sq_eq E hNne (hsumG.symm.trans hnormα)
    have h2 : Nat.card ↥N * ∑ ψ : ↥(Work.CharCore.Irr ↥I), (F ψ) ^ 2 = Nat.card ↥I :=
      corr_nat_mul_sum_sq_eq F hNne (hsumI.symm.trans hnormβ)
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hNne) (h1.trans h2.symm)
  -- the expansions of `β` and `α`
  have hβexp : indFun (N.subgroupOf I) θI
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I), (F ψ : ℂ) • (ψ : ↥I → ℂ) := by
    conv_lhs => rw [corr_classFun_eq_sum_irr (corr_isClassFun_indFun (N.subgroupOf I) θI)]
    exact Finset.sum_congr rfl fun ψ _ => by rw [hF ψ]
  have hαexp : indFun N θ
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I), (F ψ : ℂ) • indFun I (ψ : ↥I → ℂ) := by
    rw [hαβ, hβexp, corr_indFun_sum I Finset.univ (fun ψ => (F ψ : ℂ) • (ψ : ↥I → ℂ))]
    exact Finset.sum_congr rfl fun ψ _ => corr_indFun_smul I (F ψ) (ψ : ↥I → ℂ)
  -- the multiplicity identity
  have hmult : ∀ χ : ↥(Work.CharCore.Irr G), E χ
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I), a χ ψ * F ψ := by
    intro χ
    have h1 : (E χ : ℂ) = ∑ ψ : ↥(Work.CharCore.Irr ↥I), (a χ ψ : ℂ) * (F ψ : ℂ) := by
      rw [← hE χ, hαexp, cfInner_sum_smul_left]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [ha χ ψ]
      ring
    have h2 : ((∑ ψ : ↥(Work.CharCore.Irr ↥I), a χ ψ * F ψ : ℕ) : ℂ) = (E χ : ℂ) := by
      push_cast
      exact h1.symm
    exact (Nat.cast_injective (R := ℂ) h2).symm
  -- identifications of the multiplicities with the indicators of "lying over"
  have hres_eq : ∀ ψ : ↥I → ℂ,
      (fun x : ↥(N.subgroupOf I) => (resFunOfLe hNI ψ) (Subgroup.subgroupOfEquivOfLe hNI x))
        = resFun (N.subgroupOf I) ψ := by
    intro ψ
    funext x
    show ψ ⟨(Subgroup.subgroupOfEquivOfLe hNI x : ↥N), hNI (Subgroup.subgroupOfEquivOfLe hNI x).2⟩
      = ψ x
    congr 1
  have hLieF : ∀ ψ : ↥(Work.CharCore.Irr ↥I),
      (IsConstituentOf θ (resFunOfLe hNI (ψ : ↥I → ℂ)) ↔ F ψ ≠ 0) := by
    intro ψ
    have hcf : cfInner (indFun (N.subgroupOf I) θI) (ψ : ↥I → ℂ)
        = starRingEnd ℂ (cfInner (resFunOfLe hNI (ψ : ↥I → ℂ)) θ) := by
      rw [cfInner_indFun (H := N.subgroupOf I) θI
        (Work.CharCore.isClassFun_of_mem_Irr ψ.2), cfInner_conj_symm]
      congr 1
      rw [← hres_eq (ψ : ↥I → ℂ)]
      exact corr_cfInner_comp_mulEquiv (Subgroup.subgroupOfEquivOfLe hNI)
        (resFunOfLe hNI (ψ : ↥I → ℂ)) θ
    have h1 : IsConstituentOf θ (resFunOfLe hNI (ψ : ↥I → ℂ))
        ↔ cfInner (indFun (N.subgroupOf I) θI) (ψ : ↥I → ℂ) ≠ 0 := by
      rw [IsConstituentOf, hcf]
      exact ⟨fun hz hx => hz ((starRingEnd ℂ).injective (by rw [hx, map_zero])),
        fun hz hx => hz (by rw [hx]; simp)⟩
    rw [h1, hF ψ, Nat.cast_ne_zero]
  -- the induction half, or: the indicator form of the multiplicity identity
  have hind : ∀ ψ : ↥(Work.CharCore.Irr ↥I), F ψ ≠ 0 →
      indFun I (ψ : ↥I → ℂ) ∈ Irr G := by
    intro ψ hf
    have hlie : LiesOver N I hNI θ (ψ : ↥I → ℂ) :=
      (corr_liesOver_iff hNI θ (ψ : ↥I → ℂ)).mpr ((hLieF ψ).mpr hf)
    exact clifford_induction_mem_Irr (G := G) (N := N) hθ ((corr_mem_Irr_charCore).mpr ψ.2) hlie
  have hkey' : ∀ χ : ↥(Work.CharCore.Irr G), E χ
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I),
          (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) := by
    intro χ
    rw [hmult χ]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    by_cases hf : F ψ = 0
    · simp [hf]
    · have hmem : indFun I (ψ : ↥I → ℂ) ∈ Work.CharCore.Irr G :=
        (corr_mem_Irr_charCore).mp (hind ψ hf)
      by_cases hχeq : indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ)
      · have ha1 : a χ ψ = 1 := by
          refine Nat.cast_injective (R := ℂ) ?_
          have h1 : ((a χ ψ : ℕ) : ℂ) = 1 := by
            rw [← ha χ ψ, hχeq,
              cfInner_eq_ite_of_mem_Irr ((corr_mem_Irr_charCore).mpr χ.2)
                ((corr_mem_Irr_charCore).mpr χ.2)]
            simp
          simpa using h1
        rw [if_pos hχeq, ha1, one_mul]
      · have ha0 : a χ ψ = 0 := by
          refine Nat.cast_injective (R := ℂ) ?_
          have h1 : ((a χ ψ : ℕ) : ℂ) = 0 := by
            rw [← ha χ ψ,
              cfInner_eq_ite_of_mem_Irr ((corr_mem_Irr_charCore).mpr hmem)
                ((corr_mem_Irr_charCore).mpr χ.2)]
            simp [hχeq]
          simpa using h1
        rw [if_neg hχeq, ha0, zero_mul]
  -- injectivity of the fibre map
  have hfib1 : ∑ χ : ↥(Work.CharCore.Irr G), ∑ ψ : ↥(Work.CharCore.Irr ↥I),
        (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) ^ 2
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I), (F ψ) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    by_cases hf : F ψ = 0
    · simp [hf]
    · have hmem : indFun I (ψ : ↥I → ℂ) ∈ Work.CharCore.Irr G :=
        (corr_mem_Irr_charCore).mp (hind ψ hf)
      let χ₀ : ↥(Work.CharCore.Irr G) := ⟨indFun I (ψ : ↥I → ℂ), hmem⟩
      have hχ₀ : (χ₀ : G → ℂ) = indFun I (ψ : ↥I → ℂ) := rfl
      rw [Finset.sum_eq_single χ₀]
      · rw [if_pos hχ₀.symm, pow_two]
      · intro χ _ hne
        have hfalse : ¬ (indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ)) := by
          intro hcon
          exact hne (Subtype.ext (hcon.symm.trans hχ₀))
        rw [if_neg hfalse]
        simp
      · intro hm; exact absurd (Finset.mem_univ χ₀) hm
  have hsumbig : ∑ χ : ↥(Work.CharCore.Irr G),
        (∑ ψ : ↥(Work.CharCore.Irr ↥I),
          (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)) ^ 2
      = ∑ ψ : ↥(Work.CharCore.Irr ↥I), (F ψ) ^ 2 := by
    rw [← hsum_eq]
    exact Finset.sum_congr rfl fun χ _ => by rw [← hkey' χ]
  have hcs : ∀ χ ∈ (Finset.univ : Finset ↥(Work.CharCore.Irr G)),
      (∑ ψ : ↥(Work.CharCore.Irr ↥I),
          (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)) ^ 2
        ≥ ∑ ψ : ↥(Work.CharCore.Irr ↥I),
          (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) ^ 2 := by
    intro χ _
    have hstep : ∀ ψ : ↥(Work.CharCore.Irr ↥I),
        (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)
          * (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)
        ≤ ∑ ψ' : ↥(Work.CharCore.Irr ↥I),
            (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)
              * (if indFun I (ψ' : ↥I → ℂ) = (χ : G → ℂ) then F ψ' else 0) :=
      fun ψ => by
        apply Finset.single_le_sum (f := fun ψ' : ↥(Work.CharCore.Irr ↥I) =>
          (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)
            * (if indFun I (ψ' : ↥I → ℂ) = (χ : G → ℂ) then F ψ' else 0))
        · intro a _
          exact Nat.zero_le _
        · exact Finset.mem_univ ψ
    calc ∑ ψ : ↥(Work.CharCore.Irr ↥I),
            (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) ^ 2
        = ∑ ψ : ↥(Work.CharCore.Irr ↥I),
            (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)
              * (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) := by
          simp only [pow_two]
      _ ≤ ∑ ψ : ↥(Work.CharCore.Irr ↥I), ∑ ψ' : ↥(Work.CharCore.Irr ↥I),
            (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)
              * (if indFun I (ψ' : ↥I → ℂ) = (χ : G → ℂ) then F ψ' else 0) :=
          Finset.sum_le_sum fun ψ _ => hstep ψ
      _ = (∑ ψ : ↥(Work.CharCore.Irr ↥I),
              (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0))
            * (∑ ψ : ↥(Work.CharCore.Irr ↥I),
              (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)) := by
          rw [Finset.sum_mul_sum]
      _ = (∑ ψ : ↥(Work.CharCore.Irr ↥I),
              (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)) ^ 2 := by
          simp only [pow_two]
  have hterm : ∀ χ : ↥(Work.CharCore.Irr G),
      (∑ ψ : ↥(Work.CharCore.Irr ↥I),
          (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)) ^ 2
        = ∑ ψ : ↥(Work.CharCore.Irr ↥I),
          (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) ^ 2 := by
    have htot : (∑ χ : ↥(Work.CharCore.Irr G),
          (∑ ψ : ↥(Work.CharCore.Irr ↥I),
            (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)) ^ 2)
        = ∑ χ : ↥(Work.CharCore.Irr G), ∑ ψ : ↥(Work.CharCore.Irr ↥I),
            (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) ^ 2 := by
      rw [hsumbig, hfib1]
    intro χ
    exact ((Finset.sum_eq_sum_iff_of_le hcs).mp htot.symm χ (Finset.mem_univ χ)).symm
  have huniq : ∀ χ : ↥(Work.CharCore.Irr G), ∀ ψ ψ' : ↥(Work.CharCore.Irr ↥I),
      (if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0) ≠ 0 →
      (if indFun I (ψ' : ↥I → ℂ) = (χ : G → ℂ) then F ψ' else 0) ≠ 0 → ψ = ψ' := by
    intro χ ψ ψ' h1 h2
    exact nat_sum_sq_eq_imp_eq
      (fun ψ : ↥(Work.CharCore.Irr ↥I) =>
        if indFun I (ψ : ↥I → ℂ) = (χ : G → ℂ) then F ψ else 0)
      (hterm χ) ψ ψ' h1 h2
  have huniqF : ∀ ψ ψ' : ↥(Work.CharCore.Irr ↥I), F ψ ≠ 0 → F ψ' ≠ 0 →
      indFun I (ψ : ↥I → ℂ) = indFun I (ψ' : ↥I → ℂ) → ψ = ψ' := by
    intro ψ ψ' hf hf' heq
    have hmem : indFun I (ψ : ↥I → ℂ) ∈ Work.CharCore.Irr G :=
      (corr_mem_Irr_charCore).mp (hind ψ hf)
    have h1 : (if indFun I (ψ : ↥I → ℂ) = (⟨indFun I (ψ : ↥I → ℂ), hmem⟩ : ↥(Work.CharCore.Irr G))
        then F ψ else 0) ≠ 0 := by
      rw [if_pos rfl]; exact hf
    have h2 : (if indFun I (ψ' : ↥I → ℂ)
        = (⟨indFun I (ψ : ↥I → ℂ), hmem⟩ : ↥(Work.CharCore.Irr G)) then F ψ' else 0) ≠ 0 := by
      rw [if_pos heq.symm]; exact hf'
    exact huniq ⟨indFun I (ψ : ↥I → ℂ), hmem⟩ ψ ψ' h1 h2
  -- existence
  have hEne : E ⟨χ, hχC⟩ ≠ 0 := by
    intro h0
    have h1 : cfInner (indFun N θ) χ = 0 := by rw [hE ⟨χ, hχC⟩, h0, Nat.cast_zero]
    rw [cfInner_indFun θ (IsClassFun.of_mem_Irr hχ), cfInner_conj_symm] at h1
    exact h ((starRingEnd ℂ).injective (by rw [h1, map_zero]))
  set χc : ↥(Work.CharCore.Irr G) := ⟨χ, hχC⟩ with hχc
  obtain ⟨ψ₀, hInd₀, hF₀⟩ : ∃ ψ : ↥(Work.CharCore.Irr ↥I),
      indFun I (ψ : ↥I → ℂ) = χ ∧ F ψ ≠ 0 := by
    have h1 : (∑ ψ : ↥(Work.CharCore.Irr ↥I),
        (if indFun I (ψ : ↥I → ℂ) = (χc : G → ℂ) then F ψ else 0)) ≠ 0 := by
      rw [← hkey' χc]
      exact hEne
    obtain ⟨ψ, -, hψ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have hcond : indFun I (ψ : ↥I → ℂ) = χ := by
      by_contra hc
      rw [if_neg hc] at hψ
      exact hψ rfl
    exact ⟨ψ, hcond, by rwa [if_pos hcond] at hψ⟩
  refine ⟨(ψ₀ : ↥I → ℂ), ⟨(corr_mem_Irr_charCore).mpr ψ₀.2,
    (corr_liesOver_iff hNI θ (ψ₀ : ↥I → ℂ)).mpr ((hLieF ψ₀).mpr hF₀), hInd₀⟩, ?_⟩
  intro ψ hψ
  obtain ⟨hψIrr, hψlie, hψind⟩ := hψ
  have hψC : ψ ∈ Work.CharCore.Irr ↥I := (corr_mem_Irr_charCore).mp hψIrr
  have hFne : F ⟨ψ, hψC⟩ ≠ 0 := (hLieF ⟨ψ, hψC⟩).mp ((corr_liesOver_iff hNI θ ψ).mp hψlie)
  exact (congrArg Subtype.val (huniqF ψ₀ ⟨ψ, hψC⟩ hF₀ hFne (hInd₀.trans hψind.symm))).symm

end Work.Clifford
