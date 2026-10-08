import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.Higman.higman_lemma3_base
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma3_delta
import Submission.Work.Higman.higman_lemma3_phi
import Submission.Work.Higman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- If `ξ u ≡ u (mod A)` then also `ξ⁻¹ u ≡ u (mod A)`. -/
private lemma xi_symm_mul_inv_mem {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {u : P} (htriv : h.xi u * u⁻¹ ∈ A) :
    (h.xi : MulAut P).symm u * u⁻¹ ∈ A := by
  have h1 : (h.xi : MulAut P).symm (h.xi u * u⁻¹) ∈ A :=
    symm_mem_of_map_eq h.xi hA.map_eq htriv
  have h2 : (h.xi : MulAut P).symm (h.xi u * u⁻¹) = u * ((h.xi : MulAut P).symm u)⁻¹ := by
    simp
  rw [h2] at h1
  have h3 := A.inv_mem h1
  simpa only [mul_inv_rev, inv_inv] using h3

/-- The `A`-element `u⁻¹ * ξ u`, which makes `ξ u = u * (u⁻¹ * ξ u)`. -/
private lemma inv_xi_mem {h : IsSuzuki2Grp P} {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {u : P} (htriv : h.xi u * u⁻¹ ∈ A) : u⁻¹ * h.xi u ∈ A := by
  have h1 : u⁻¹ * (h.xi u * u⁻¹) * u ∈ A := by
    simpa [inv_inv] using hA.normal.conj_mem (h.xi u * u⁻¹) htriv u⁻¹
  have h2 : u⁻¹ * (h.xi u * u⁻¹) * u = u⁻¹ * h.xi u := by group
  rwa [h2] at h1

/-- `ξ` maps the values `φ_u(a)` into `φ_u(A)` (only `ξ u ≡ u (mod A)` is used). -/
private lemma phiA_xi_map_le_triv {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {u : P} (htriv : h.xi u * u⁻¹ ∈ A) :
    (phiA u A).map (h.xi : MulAut P).toMonoidHom ≤ phiA u A := by
  have hAb := hA.abelian
  rw [Subgroup.map_le_iff_le_comap, phiA, Subgroup.closure_le]
  rintro y ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  show h.xi (phiVal u a) ∈ phiA u A
  rw [phiVal_xi]
  have hxa : h.xi a ∈ A := by
    have hh := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom ha
    rwa [hA.map_eq] at hh
  have hconj : (h.xi u)⁻¹ * (h.xi a) * (h.xi u) = u⁻¹ * (h.xi a) * u :=
    coset_conj_eq hAb htriv hxa
  rw [phiVal, hconj]
  exact Subgroup.subset_closure ⟨h.xi a, hxa, rfl⟩

/-- `ξ⁻¹` maps the values `φ_u(a)` into `φ_u(A)` (only `ξ u ≡ u (mod A)` is used). -/
private lemma phiA_xi_map_le_inv {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {u : P} (htriv : h.xi u * u⁻¹ ∈ A) :
    (phiA u A).map ((h.xi : MulAut P).symm).toMonoidHom ≤ phiA u A := by
  have hAb := hA.abelian
  have hb1 := xi_symm_mul_inv_mem hA htriv
  rw [Subgroup.map_le_iff_le_comap, phiA, Subgroup.closure_le]
  rintro y ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  show (h.xi : MulAut P).symm (phiVal u a) ∈ phiA u A
  have hsymm : (h.xi : MulAut P).symm (phiVal u a)
      = phiVal ((h.xi : MulAut P).symm u) ((h.xi : MulAut P).symm a) := by
    apply (h.xi : MulAut P).injective
    rw [MulEquiv.apply_symm_apply, phiVal_xi]
    simp
  rw [hsymm]
  have hxa : (h.xi : MulAut P).symm a ∈ A := symm_mem_of_map_eq h.xi hA.map_eq ha
  rw [phiVal, coset_conj_eq hAb hb1 hxa]
  exact Subgroup.subset_closure ⟨(h.xi : MulAut P).symm a, hxa, rfl⟩

/-- `φ_u(A)` is `ξ`-invariant (only `ξ u ≡ u (mod A)` is used). -/
private lemma phiA_xi_inv_triv {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {u : P} (htriv : h.xi u * u⁻¹ ∈ A) :
    (phiA u A).map (h.xi : MulAut P).toMonoidHom = phiA u A := by
  refine Subgroup.eq_of_le_of_card_ge (phiA_xi_map_le_triv hA htriv) ?_
  rw [Subgroup.card_map_of_injective (h.xi : MulAut P).injective]

/-- `⟨φ_u(A), u²⟩` is `ξ`-invariant (only `ξ u ≡ u (mod A)` is used). -/
private lemma Bsub_xi_inv_triv {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {u : P} (htriv : h.xi u * u⁻¹ ∈ A) (hu2A : u ^ 2 ∈ A) :
    (Bsub u A).map (h.xi : MulAut P).toMonoidHom = Bsub u A := by
  have hAn := hA.normal
  have hAb := hA.abelian
  have hsub1 : (Bsub u A).map (h.xi : MulAut P).toMonoidHom ≤ Bsub u A := by
    rw [Bsub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact mem_Bsub_left (phiA_xi_map_le_triv hA htriv (Subgroup.mem_map_of_mem _ hz))
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [map_pow]
      change (h.xi : MulAut P) u ^ 2 ∈ Subgroup.closure ((phiA u A : Set P) ∪ {u ^ 2})
      have hmem : u⁻¹ * h.xi u ∈ A := inv_xi_mem hA htriv
      have h1 : (h.xi u) ^ 2 = u ^ 2 * phiVal u (u⁻¹ * h.xi u) := by
        conv_lhs => rw [show h.xi u = u * (u⁻¹ * h.xi u) from by group]
        exact sq_mul_eq_phiVal' hAn hAb hmem
      rw [h1]
      exact Subgroup.mul_mem _ mem_Bsub_sq
        (mem_Bsub_left (Subgroup.subset_closure ⟨u⁻¹ * h.xi u, hmem, rfl⟩))
  have hsub2 : (Bsub u A).map ((h.xi : MulAut P).symm).toMonoidHom ≤ Bsub u A := by
    rw [Bsub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact mem_Bsub_left (phiA_xi_map_le_inv hA htriv (Subgroup.mem_map_of_mem _ hz))
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [map_pow]
      change (h.xi : MulAut P).symm u ^ 2 ∈ Subgroup.closure ((phiA u A : Set P) ∪ {u ^ 2})
      have hb1 : (h.xi : MulAut P).symm u * u⁻¹ ∈ A := xi_symm_mul_inv_mem hA htriv
      have hmem : u⁻¹ * (h.xi : MulAut P).symm u ∈ A := by
        have h1 := hAn.conj_mem ((h.xi : MulAut P).symm u * u⁻¹) hb1 u⁻¹
        rw [inv_inv] at h1
        have h2 : u⁻¹ * ((h.xi : MulAut P).symm u * u⁻¹) * u
            = u⁻¹ * (h.xi : MulAut P).symm u := by group
        rwa [h2] at h1
      have h1 : ((h.xi : MulAut P).symm u) ^ 2
          = u ^ 2 * phiVal u (u⁻¹ * (h.xi : MulAut P).symm u) := by
        conv_lhs => rw [show (h.xi : MulAut P).symm u = u * (u⁻¹ * (h.xi : MulAut P).symm u)
          from by group]
        exact sq_mul_eq_phiVal' hAn hAb hmem
      rw [h1]
      exact Subgroup.mul_mem _ mem_Bsub_sq
        (mem_Bsub_left (Subgroup.subset_closure ⟨u⁻¹ * (h.xi : MulAut P).symm u, hmem, rfl⟩))
  refine le_antisymm hsub1 ?_
  intro x hx
  exact ⟨(h.xi : MulAut P).symm x, hsub2 (Subgroup.mem_map_of_mem _ hx), by simp⟩

/-- **Last step of Higman (1963), Lemma 3.**  Let `A` be a `ξ`-abelian-normal subgroup of a
Suzuki 2-group with `Ω₁(P) ≤ A`, let `C ≥ A` be a subgroup with `C² ≤ A²`, and let `u ∈ C \ A`
satisfy
* `ξ u ≡ u (mod A)` (`htriv`), and
* `ν̄_u = id`: for every `a ∈ A` there is `x ∈ A` with `x * x = u⁻¹ * a * u * a⁻¹` and
  `x ≡ a (mod A²)` (`hnu`).
Then `False`.

Proof sketch (Higman, p. 84).  Put `δ_u(a) = u⁻¹ a u a⁻¹ = ν_u(a)²` and
`Φ(a) = a² · δ_u(a) = (a · ν_u(a))²`.  `Φ : A → A⁴` is a homomorphism (`δ_u` is multiplicative
because `A` is abelian) and `(u a)² = u² · Φ(a)` for all `a ∈ A` (`u⁻¹ a u = a δ_u(a)`).

*Derive `u² ∈ A⁴`.*  `htriv` gives `ξ u = u a₀` with `a₀ ∈ A`, and `C² ≤ A²` gives `u² ∈ A²`.
So `ξ(u²) = (ξu)² = u² · Φ(a₀)` with `Φ(a₀) ∈ A⁴`.  Since `ξ` fixes the `A²`-coset of `u²` and
acts transitively on the non-trivial elements of `A/A²` (`xi_trans_quot_sq`), while
`|A/A²| = |A ⊓ Ω₁| = |Ω₁| ≥ 4` (`hOm`, `omega1_card_ge_four`, `mem_powSub_two_iff`), we get
`u² ∈ A⁴`.

*Conclude.*  If `u² ∈ Φ(A)` then there is `a ∈ A` with `Φ(a) = u⁻²`, so
`(u a)² = u² Φ(a) = 1`; all involutions of `P` lie in `Ω₁(P) ≤ A`, so `u a ∈ A` and
`u = (ua) a⁻¹ ∈ A`, contradiction with `huA`.
If `u² ∉ Φ(A)`: the subgroup `B = ⟨(C∖A)²⟩ = ⟨u², Φ(A)⟩ ≤ A²` is `ξ`-invariant (since `ξ`
permutes `C∖A`) and `B/Φ(A)` is cyclic, so `B = A ^ (2^s)` by Higman's Lemma 1
(`HomocyclicData.hstruct`); since `Φ(A) ⊆ A⁴ ≤ B` and `B/Φ(A)` cyclic, its quotient `A²/A⁴`
(if `B = A²`) — or more directly the chain `A ^ (2^j)/A ^ (2^i) ≅ (ℤ/2)^n` of `hstruct` — would be
cyclic, forcing `n ≤ 1` against `|A ⊓ Ω₁| ≥ 4`. -/
theorem higman_lemma3_last_step {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hOm : Work.Higman.omega1 P ≤ A)
    (hC2 : Work.Higman.powSub C 2 ≤ Work.Higman.powSub A 2)
    {u : P} (huC : u ∈ C) (huA : u ∉ A)
    (htriv : h.xi u * u⁻¹ ∈ A)
    (hnu : ∀ a ∈ A, ∃ x ∈ A, x * x = u⁻¹ * a * u * a⁻¹
      ∧ x * a⁻¹ ∈ Work.Higman.powSub A 2) :
    False := by
  classical
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  -- `u² ∈ A`
  have hu2A : u ^ 2 ∈ A := by
    have h1 : u ^ 2 ∈ powSub C 2 := pow_mem_powSub (A := C) (n := 2) huC
    exact powSub_le (A := A) (n := 2) (by norm_num) (hC2 h1)
  have hu2ne : u ^ 2 ≠ 1 := by
    intro h1
    exact huA (hOm (h.mem_omega1.mpr h1))
  -- `|A ⊓ Ω₁(P)| ≥ 4`
  have hq : 4 ≤ qcard A := by
    have h1 : A ⊓ omega1 P = omega1 P := le_antisymm inf_le_right (le_inf hOm le_rfl)
    rw [qcard, h1]
    exact h.omega1_card_ge_four
  obtain ⟨D⟩ := exists_homocyclicData h hA
  have hKinv : (phiA u A).map (h.xi : MulAut P).toMonoidHom = phiA u A :=
    phiA_xi_inv_triv hA htriv
  have hBinv : (Bsub u A).map (h.xi : MulAut P).toMonoidHom = Bsub u A :=
    Bsub_xi_inv_triv hA htriv hu2A
  have hKle : phiA u A ≤ A := phiA_le hAn u
  have hBle : Bsub u A ≤ A := Bsub_le hAn hu2A
  have hKleB : phiA u A ≤ Bsub u A := fun _ hy => mem_Bsub_left hy
  by_cases hcase : u ^ 2 ∈ phiA u A
  · -- ## Case A: `u² ∈ Φ(A)`
    obtain ⟨a, ha, haval⟩ := (mem_phiA hAn hAb u).mp ((phiA u A).inv_mem hcase)
    have h1 : (u * a) ^ 2 = 1 := by
      rw [sq_mul_eq_phiVal' hAn hAb ha, ← haval, mul_inv_cancel]
    have h2 : u * a ∈ omega1 P := h.mem_omega1.mpr h1
    exact huA (by
      have h3 : u * a ∈ A := hOm h2
      have h4 : u = (u * a) * a⁻¹ := by group
      rw [h4]
      exact A.mul_mem h3 (A.inv_mem ha))
  · -- ## Case B: `u² ∉ Φ(A)`
    obtain ⟨s, hsle, hs⟩ := D.hstruct (Bsub u A) hBle hBinv
    obtain ⟨t, htle, ht⟩ := D.hstruct (phiA u A) hKle hKinv
    have hBne : Bsub u A ≠ ⊥ := by
      intro hbot
      exact hu2ne (Subgroup.mem_bot.mp (hbot ▸ mem_Bsub_sq))
    have hslt : s < D.e := by
      by_contra hcon
      push Not at hcon
      exact hBne (by rw [hs, powSub_eq_bot_of_exp hAb hcon D.hexp])
    -- the exponent indices satisfy `s ≤ t`
    have htge : s ≤ t := by
      by_contra hcon
      push Not at hcon
      have hBK : Bsub u A ≤ phiA u A := by
        rw [hs, ht]
        exact powSub_le_of_dvd hAb (Nat.pow_dvd_pow 2 hcon.le)
      exact hcase (hBK mem_Bsub_sq)
    have hts : s < t := by
      rcases lt_or_eq_of_le htge with hlt | heq
      · exact hlt
      · exfalso
        apply hcase
        rw [ht, ← heq, ← hs]
        exact mem_Bsub_sq
    have ht1 : s + 1 ≤ t := hts
    -- `Φ(A) ⊆ B²`
    have hphi : phiA u A ≤ powSub (Bsub u A) 2 := by
      rw [ht, hs, powSub_powSub hAb]
      have h2 : 2 ^ s * 2 = 2 ^ (s + 1) := by rw [← pow_succ]
      rw [h2]
      exact powSub_le_of_dvd hAb (Nat.pow_dvd_pow 2 ht1)
    -- `B` is covered by two cosets of `B²`
    have hsub : (Bsub u A : Set P) ⊆ (powSub (Bsub u A) 2 : Set P) ∪
        (fun z => z * u ^ 2) '' (powSub (Bsub u A) 2 : Set P) := by
      intro y hy
      rcases Bsub_sq_cover hAn hAb hu2A hphi hy with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨y * (u ^ 2)⁻¹, h1, by group⟩
    have hcard_le : Nat.card ↥(Bsub u A) ≤ 2 * Nat.card ↥(powSub (Bsub u A) 2) :=
      nat_card_le_two_mul_of_subset_two_cosets hsub
    -- cardinalities in terms of `qcard A`
    have hcard1 : Nat.card ↥(Bsub u A) = (qcard A) ^ (D.e - s) := by
      rw [hs]; exact D.hcard s hsle
    have hcard2 : Nat.card ↥(powSub (Bsub u A) 2) = (qcard A) ^ (D.e - s - 1) := by
      have h3 : D.e - (s + 1) = D.e - s - 1 := by omega
      rw [hs, powSub_powSub hAb]
      rw [show 2 ^ s * 2 = 2 ^ (s + 1) from by rw [← pow_succ]]
      rw [D.hcard (s + 1) (by omega), h3]
    rw [hcard1, hcard2] at hcard_le
    -- `qcard A ≤ 2`, contradicting `hq`
    have hQle2 : qcard A ≤ 2 := by
      have hpos : 0 < (qcard A) ^ (D.e - s - 1) := pow_pos (by omega) _
      have hkey : (qcard A) * (qcard A) ^ (D.e - s - 1) = (qcard A) ^ (D.e - s) := by
        rw [mul_comm, ← pow_succ]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ D.e - s)]
      have hlt : (qcard A) ^ (D.e - s) < (qcard A) ^ (D.e - s) :=
        calc (qcard A) ^ (D.e - s) ≤ 2 * (qcard A) ^ (D.e - s - 1) := hcard_le
          _ < 4 * (qcard A) ^ (D.e - s - 1) := Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
          _ ≤ (qcard A) * (qcard A) ^ (D.e - s - 1) := Nat.mul_le_mul_right _ (by omega)
          _ = (qcard A) ^ (D.e - s) := hkey
      exact absurd hlt (lt_irrefl _)
    omega

end Work.Higman
