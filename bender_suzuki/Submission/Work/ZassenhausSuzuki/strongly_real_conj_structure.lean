import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerData
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausSuzuki.SL2ModelClass
import Submission.Work.ZassenhausSuzuki.SL2SingerConj
import Submission.Work.ZassenhausSuzuki.Shadow.X5isoPSL2_of
import Submission.Work.Models.PSL2.pslEquiv
import Submission.Work.Models.PSL2.D_facts
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.singer_cycle_model
import Submission.Work.ZassenhausSuzuki.QSZ_isCyclic_twoPoint
import Submission.Work.ZassenhausSuzuki.Q0sub_card_eq_center_card
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ThmF.ChV12.lemma4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ZassenhausSuzuki

/-!
Suzuki 1962, §8, p. 118: in a Zassenhaus split rank-one configuration `H = Q ⋊ D` with `Q` a
non-abelian `2`-group and `σ = ρ` in the structure identity (encoded by `SzHyp`), every strongly
real element `x` (a product of two involutions) with `x * x ≠ 1` is conjugate into `Q`, into the
two-point stabiliser `twoPoint H t`, or into the Singer cycle `S.V ≤ X5 H t = ⟨Q₀,K,t⟩ ≅ LF(2,q)`.

Route: Proposition 13 (`Work.ThmF.ChV12.exists_conj_eq_inv_mul_t`) reduces `x` to `u * t` with
`u` an involution of `Q0sub H`; then `u * t ∈ X5 H t`.  It remains to classify `u * t ∈ X5`.  In
`X5 H t ≅ PSL2Model n` (`Work.ZassenhausSuzuki.Shadow.ChV12.X5isoPSL2_of`, `|Q0sub H| = 2^n`) the class of a matrix
of `SL(2,2ⁿ)` is determined by its characteristic polynomial: trace `0` (unipotent), two
eigenvalues in `GF(2ⁿ)` (split torus), or two eigenvalues in `GF(2^{2n}) ∖ GF(2ⁿ)` of norm `1`
(a Singer cycle, the model of `S.V`).
-/
theorem strongly_real_conj_structure {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s : G} (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (S : Work.ZassenhausSuzuki.SingerCycle.Data G H t)
    {x : G} (hx2 : x * x ≠ 1)
    (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x) :
    (∃ g : G, g * x * g⁻¹ ∈ Q) ∨
      (∃ g : G, g * x * g⁻¹ ∈ Submission.Blueprint.twoPoint H t) ∨
      (∃ g : G, g * x * g⁻¹ ∈ S.V) := by
  classical
  -- the model `X5 H t ≃ SL(2, 2ⁿ)`
  obtain ⟨n, hn, hqcard, ⟨e⟩⟩ := Work.ZassenhausSuzuki.Shadow.ChV12.X5isoPSL2_of h
  obtain ⟨ψ⟩ := Work.Models.PSL2.pslEquiv n
  set Ψ : ↥(Work.ThmF.Lemma5.X5 H t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := e.trans ψ.symm with hΨ
  have hFcard : Nat.card (GaloisField 2 n) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [GaloisField.card 2 n (by omega), hqcard]
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hFcard, hqcard]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  -- `|twoPoint H t| = q - 1`
  have htwo : Nat.card ↥(Submission.Blueprint.twoPoint H t)
      = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
    have hd := twoPoint_card_eq_involutions (H := H) (Q := Q) (t := t) h.split h.zass h.two
    have hInv : Submission.Blueprint.involutions (Q : Set G)
        = Submission.Blueprint.involutions (H : Set G) := by
      ext z
      constructor
      · intro hz; exact ⟨h.split.le hz.1, hz.2⟩
      · intro hz
        have hz' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h.split h.two z hz)
        exact ⟨hz'.1, hz.2⟩
    rw [hd, hInv]
    have hc := Q0sub_card_eq_involutions_add_one h.split h.two
    omega
  -- Proposition 13: `x` is conjugate to `u * t`, `u` a non-trivial element of `Q₀`
  obtain ⟨u, huQ0, hu1, g₀, hg₀⟩ :=
    Work.ThmF.ChV12.exists_conj_eq_inv_mul_t h.split.stronglyEmbedded h.split.twoTransitive
      h.split.invol h.split.not_mem
      (Work.ThmF.ChV12.involution_commute_conj (Work.ZassenhausSuzuki.SzHyp.hcomm h)) hx2 hsr
  set y : G := u * t with hy
  have hyX5 : y ∈ Work.ThmF.Lemma5.X5 H t := by
    rw [hy]
    exact mul_mem (Work.ThmF.Lemma5.Q0_subset_X5 H t huQ0)
      (Work.ThmF.Lemma5.t_mem_X5 H t)
  have hyy : y * y ≠ 1 := by
    rw [hy]
    intro hc
    apply hx2
    have h3 : g₀ * (x * x) * g₀⁻¹ = 1 := by
      rw [show g₀ * (x * x) * g₀⁻¹
          = (g₀ * x * g₀⁻¹) * (g₀ * x * g₀⁻¹) by group, hg₀, hc]
    calc x * x = g₀⁻¹ * (g₀ * (x * x) * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h3]; group
  -- the corresponding matrix
  set a : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := Ψ ⟨y, hyX5⟩ with ha
  have haa : a * a ≠ 1 := by
    intro hc
    apply hyy
    have h1 : (⟨y, hyX5⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * ⟨y, hyX5⟩ = 1 := by
      apply Ψ.injective
      rw [map_mul, map_one, ← ha]
      exact hc
    simpa using congrArg (fun z : ↥(Work.ThmF.Lemma5.X5 H t) => (z : G)) h1
  -- the transport of a conjugacy statement from `SL(2, F)` back to `G`
  have transport : ∀ (A : Subgroup G), A ≤ Work.ThmF.Lemma5.X5 H t →
      ∀ m : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      m * a * m⁻¹ ∈ (A.subgroupOf (Work.ThmF.Lemma5.X5 H t)).map Ψ.toMonoidHom →
      ∃ g : G, g * y * g⁻¹ ∈ A := by
    intro A hAle m hm
    obtain ⟨z, hz, hzΨ⟩ := Subgroup.mem_map.mp hm
    have hzΨ' : Ψ z = m * a * m⁻¹ := hzΨ
    refine ⟨((Ψ.symm m : ↥(Work.ThmF.Lemma5.X5 H t)) : G), ?_⟩
    have h1 : z = (Ψ.symm m) * ⟨y, hyX5⟩ * (Ψ.symm m)⁻¹ := by
      apply Ψ.injective
      have h2 : Ψ ((Ψ.symm m) * ⟨y, hyX5⟩ * (Ψ.symm m)⁻¹) = m * a * m⁻¹ := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← ha]
      rw [hzΨ']
      exact h2.symm
    have h3 : (z : G) ∈ A := Subgroup.mem_subgroupOf.mp hz
    rw [h1] at h3
    simpa using h3
  rcases sl2_classify a with htr0 | ⟨k, hkD⟩ | ⟨W, hWcyc, hWcard, k, hkW⟩
  · exact absurd (sl2_trace_zero_sq_eq_one a htr0) haa
  · -- `a` is conjugate into the split torus `D ≅ twoPoint H t`
    have hAle : Submission.Blueprint.twoPoint H t ≤ Work.ThmF.Lemma5.X5 H t := by
      show (Submission.Blueprint.twoPoint H t : Set G)
        ⊆ (Work.ThmF.Lemma5.X5 H t : Set G)
      rw [← Work.ZassenhausSuzuki.SzHyp.Ksub_eq_twoPoint h]
      intro z hz
      have hz' : z ∈ Work.ThmF.Kset H t := by
        rw [← Work.ZassenhausSuzuki.SzHyp.Ksub_eq_Kset h]
        exact hz
      exact Work.ThmF.Lemma5.Kset_subset_X5 H t hz'
    have hAcyc : IsCyclic ↥(Submission.Blueprint.twoPoint H t) :=
      QSZ_isCyclic_twoPoint h.split h.zass h.two
    have hAcard : Nat.card ↥(Submission.Blueprint.twoPoint H t)
        = Nat.card (GaloisField 2 n) - 1 := by
      rw [hFcard]
      exact htwo
    have hAWcyc : IsCyclic ↥(((Submission.Blueprint.twoPoint H t).subgroupOf
        (Work.ThmF.Lemma5.X5 H t)).map Ψ.toMonoidHom) :=
      (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective)).mp
        ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hAle)).mpr hAcyc)
    have hAWcard : Nat.card ↥(((Submission.Blueprint.twoPoint H t).subgroupOf
        (Work.ThmF.Lemma5.X5 H t)).map Ψ.toMonoidHom)
        = Nat.card (GaloisField 2 n) - 1 := by
      rw [Subgroup.card_map_of_injective Ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, hAcard]
    obtain ⟨h', hh'⟩ := sl2_cyclic_conj_card_sub_one h4 hAWcyc hAWcard
      (Work.Models.PSL2.D_facts (F := GaloisField 2 n)).2
      (Work.Models.PSL2.D_facts (F := GaloisField 2 n)).1
    have hm : ∃ m : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        m * a * m⁻¹ ∈ ((Submission.Blueprint.twoPoint H t).subgroupOf
          (Work.ThmF.Lemma5.X5 H t)).map Ψ.toMonoidHom := by
      obtain ⟨aw, haw, hawD⟩ := Subgroup.mem_map.mp (hh'.symm ▸ hkD)
      refine ⟨h'⁻¹ * k, ?_⟩
      have key : (h'⁻¹ * k) * a * (h'⁻¹ * k)⁻¹ = aw := by
        have hawD' : (MulAut.conj h') aw = k * a * k⁻¹ := hawD
        have haw' : aw = (MulAut.conj h')⁻¹ (k * a * k⁻¹) := by
          calc aw = (MulAut.conj h')⁻¹ ((MulAut.conj h') aw) := by
                rw [MulAut.inv_apply_self]
            _ = (MulAut.conj h')⁻¹ (k * a * k⁻¹) := by rw [hawD']
        rw [haw']
        show h'⁻¹ * k * a * (h'⁻¹ * k)⁻¹ = (MulAut.conj h').symm (k * a * k⁻¹)
        rw [MulAut.conj_symm_apply]
        group
      rw [key]
      exact haw
    obtain ⟨m, hm⟩ := hm
    obtain ⟨g', hg'⟩ := transport (Submission.Blueprint.twoPoint H t) hAle m hm
    exact Or.inr (Or.inl ⟨g' * g₀, by
      rw [show (g' * g₀) * x * (g' * g₀)⁻¹ = g' * y * g'⁻¹ by rw [← hg₀]; group]
      exact hg'⟩)
  · -- `a` is conjugate into a Singer cycle ≅ `S.V`
    have hAle : S.V ≤ Work.ThmF.Lemma5.X5 H t := S.le_X5
    have hAcard : Nat.card ↥S.V = Nat.card (GaloisField 2 n) + 1 := by
      rw [S.card_V, hFcard]
    have hAWcyc : IsCyclic ↥((S.V.subgroupOf (Work.ThmF.Lemma5.X5 H t)).map
        Ψ.toMonoidHom) :=
      (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective)).mp
        ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hAle)).mpr S.cyclic)
    have hAWcard : Nat.card ↥((S.V.subgroupOf (Work.ThmF.Lemma5.X5 H t)).map
        Ψ.toMonoidHom) = Nat.card (GaloisField 2 n) + 1 := by
      rw [Subgroup.card_map_of_injective Ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, hAcard]
    obtain ⟨h', hh'⟩ := sl2_cyclic_conj_card_add_one h4 hAWcyc hAWcard hWcyc hWcard
    have hm : ∃ m : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        m * a * m⁻¹ ∈ (S.V.subgroupOf (Work.ThmF.Lemma5.X5 H t)).map Ψ.toMonoidHom := by
      obtain ⟨aw, haw, hawW⟩ := Subgroup.mem_map.mp (hh'.symm ▸ hkW)
      refine ⟨h'⁻¹ * k, ?_⟩
      have key : (h'⁻¹ * k) * a * (h'⁻¹ * k)⁻¹ = aw := by
        have hawW' : (MulAut.conj h') aw = k * a * k⁻¹ := hawW
        have haw' : aw = (MulAut.conj h')⁻¹ (k * a * k⁻¹) := by
          calc aw = (MulAut.conj h')⁻¹ ((MulAut.conj h') aw) := by
                rw [MulAut.inv_apply_self]
            _ = (MulAut.conj h')⁻¹ (k * a * k⁻¹) := by rw [hawW']
        rw [haw']
        show h'⁻¹ * k * a * (h'⁻¹ * k)⁻¹ = (MulAut.conj h').symm (k * a * k⁻¹)
        rw [MulAut.conj_symm_apply]
        group
      rw [key]
      exact haw
    obtain ⟨m, hm⟩ := hm
    obtain ⟨g', hg'⟩ := transport S.V hAle m hm
    exact Or.inr (Or.inr ⟨g' * g₀, by
      rw [show (g' * g₀) * x * (g' * g₀)⁻¹ = g' * y * g'⁻¹ by rw [← hg₀]; group]
      exact hg'⟩)

end Work.ZassenhausSuzuki
