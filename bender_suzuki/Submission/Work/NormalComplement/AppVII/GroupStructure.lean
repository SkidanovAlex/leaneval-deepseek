import Mathlib
import Submission.Work.Coprime.All
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.commutator_le_frattiniIn
import Submission.Work.Hering.AppVII.part1_Q_isPGroup_and_frattini
import Submission.Work.NormalComplement.AppVII.center_map_le_centralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.NormalComplement.AppVII

/-- **Coprime action with `[P,Q] = Q`.**  Let the finite group `P` act on the finite group `Q`
by conjugation (i.e. `P` normalises `Q` inside an ambient group `A`), with `Nat.card P` coprime to
`Nat.card Q`, and suppose `⁅P,Q⁆ = Q`.  Then the centraliser of `P` in `Q` lies in the derived
subgroup of `Q`.

Indeed `Q/⁅Q,Q⁆` is a finite abelian group acted on by `P` with `[P, Q/⁅Q,Q⁆] = Q/⁅Q,Q⁆`; the
coprime decomposition `M = C_M(P) · [P,M]` (`Work.Coprime.abelian_split`) therefore forces
`C_{Q/⁅Q,Q⁆}(P) = 1`, i.e. `C_Q(P) ≤ ⁅Q,Q⁆`. -/
theorem centralizer_inf_le_commutator {A : Type*} [Group A] [Finite A] (P Q : Subgroup A)
    (hQn : Q.Normal) (hcop : (Nat.card ↥P).Coprime (Nat.card ↥Q)) (hcomm : ⁅P, Q⁆ = Q) :
    Subgroup.centralizer (P : Set A) ⊓ Q ≤ ⁅Q, Q⁆ := by
  haveI : FT.Normalizes P Q := ⟨by rw [Subgroup.normalizer_eq_top Q]; exact le_top⟩
  -- the derived subgroup of `↥Q`, as a subgroup of `↥Q`
  set N : Subgroup ↥Q := commutator ↥Q with hN
  haveI hNn : N.Normal := Subgroup.commutator_normal ⊤ ⊤
  have hNchar : N.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    rw [hN, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr φ.surjective]
  haveI hNinv : FT.IsInvariant ↥P N := FT.IsInvariant.of_characteristic hNchar
  -- `[Q,P] = Q` in the abstract setting of the coprime-action library
  have hcomm' : FT.commutator ↥P (⊤ : Subgroup ↥Q) = ⊤ := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [FT.commutator_conjAction P Q, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.commutator_comm, hcomm]
  -- the image of `[Q,P]` in the abelian quotient `Q ⧸ ⁅Q,Q⁆`
  have hmap_comm : (FT.commutator ↥P (⊤ : Subgroup ↥Q)).map (QuotientGroup.mk' N)
      ≤ FT.commutator ↥P (⊤ : Subgroup (↥Q ⧸ N)) := by
    rw [Subgroup.map_le_iff_le_comap, FT.commutator_le_iff]
    intro a x _
    have h1 : (QuotientGroup.mk' N) (x⁻¹ * (a • x))
        = (QuotientGroup.mk' N x)⁻¹ * (a • (QuotientGroup.mk' N x)) := by
      simp only [map_mul, map_inv, QuotientGroup.mk'_apply, FT.quotient_smul_mk]
    show (QuotientGroup.mk' N) (x⁻¹ * (a • x)) ∈ FT.commutator ↥P (⊤ : Subgroup (↥Q ⧸ N))
    rw [h1]
    exact FT.le_commutator a (Subgroup.mem_top _)
  -- coprimality passes to the quotient
  have hcopQ : (Nat.card ↥P).Coprime (Nat.card (↥Q ⧸ N)) :=
    hcop.coprime_dvd_right (by
      refine ⟨Nat.card ↥N, ?_⟩
      rw [← Subgroup.index_eq_card]
      exact (Subgroup.index_mul_card N).symm)
  -- the coprime decomposition of the abelian quotient
  have hsplit := Work.Coprime.abelian_split ↥P hcopQ
  have hdisj : FT.fixedPoints ↥P (↥Q ⧸ N) ⊓ FT.commutator ↥P (⊤ : Subgroup (↥Q ⧸ N)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hinj : Function.Injective
        (fun y : ↥(FT.fixedPoints ↥P (↥Q ⧸ N)) ×
            ↥(FT.commutator ↥P (⊤ : Subgroup (↥Q ⧸ N))) =>
          (y.1 : ↥Q ⧸ N) * (y.2 : ↥Q ⧸ N)) := hsplit.1
    have hpair : ((⟨x, hx1⟩ : ↥(FT.fixedPoints ↥P (↥Q ⧸ N))),
        (1 : ↥(FT.commutator ↥P (⊤ : Subgroup (↥Q ⧸ N))))) =
        ((1 : ↥(FT.fixedPoints ↥P (↥Q ⧸ N))),
          (⟨x, hx2⟩ : ↥(FT.commutator ↥P (⊤ : Subgroup (↥Q ⧸ N))))) := by
      apply hinj
      simp
    have hx1' : (⟨x, hx1⟩ : FT.fixedPoints ↥P (↥Q ⧸ N)) = 1 := by
      have := congrArg Prod.fst hpair
      simpa using this
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val hx1'
  -- the image of `C_Q(P)` in the quotient is trivial, whence it lies in `⁅Q,Q⁆`
  have hfp_bot : (FT.fixedPoints ↥P ↥Q).map (QuotientGroup.mk' N) = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hdisj]
    refine le_inf (FT.map_fixedPoints_le N) ?_
    calc (FT.fixedPoints ↥P ↥Q).map (QuotientGroup.mk' N)
        ≤ (FT.commutator ↥P (⊤ : Subgroup ↥Q)).map (QuotientGroup.mk' N) :=
          Subgroup.map_mono (by rw [hcomm']; exact le_top)
      _ ≤ _ := hmap_comm
  have hle : FT.fixedPoints ↥P ↥Q ≤ N := by
    intro x hx
    have hx' : (QuotientGroup.mk' N) x ∈ (FT.fixedPoints ↥P ↥Q).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hfp_bot, Subgroup.mem_bot] at hx'
    have h2 : (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) 1 := by
      rw [map_one]; exact hx'
    have h3 : x⁻¹ * 1 ∈ N := QuotientGroup.eq.mp h2
    simpa using N.inv_mem h3
  have hmap_le : (FT.fixedPoints ↥P ↥Q).map Q.subtype ≤ N.map Q.subtype := Subgroup.map_mono hle
  rwa [FT.map_fixedPoints_conjAction P Q, Subgroup.map_subtype_commutator] at hmap_le

/-- **Peterfalvi Appendix VII, Part 1 steps 2–4.**  In the configuration `A` with `Q ◁ A`,
`P ⊓ Q = ⊥`, `P ⊔ Q = ⊤`, `|P| = p` prime, `p ∤ |Q|`, and `P` centralising every proper
`P`-invariant subgroup of `Q` (`hcent`), the subgroup `Q` is a `q`-group for a prime `q ≠ p`,
`[P,Q] = Q`, its Frattini subgroup lies in its centre, and either `Q` is abelian or `Q` is
extraspecial (`Z(Q) = [Q,Q]`) with `P` centralising `Z(Q)`. -/
theorem GroupStructure {A : Type*} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime) (hcardP : Nat.card ↥P = p)
    (hpQ : ¬ p ∣ Nat.card ↥Q) (hnotbot : ⁅P, Q⁆ ≠ ⊥)
    (hcent : ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥) :
    ⁅P, Q⁆ = Q ∧ (∃ q : ℕ, q.Prime ∧ IsPGroup q ↥Q) ∧
      frattini ↥Q ≤ Subgroup.center ↥Q ∧
      (IsMulCommutative ↥Q ∨ (Subgroup.center ↥Q = ⁅(⊤ : Subgroup ↥Q), ⊤⁆ ∧
        (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.centralizer (P : Set A))) := by
  have hPcard : (Nat.card ↥P).Prime := hcardP ▸ hp
  have hpQ' : ¬ Nat.card ↥P ∣ Nat.card ↥Q := by rw [hcardP]; exact hpQ
  have hcop : (Nat.card ↥P).Coprime (Nat.card ↥Q) := hPcard.coprime_iff_not_dvd.mpr hpQ'
  obtain ⟨hQp, hPQ, hPart3⟩ :=
    Work.Hering.AppVII.part1_Q_isPGroup_and_frattini P Q hQn hsup hinf hPcard hpQ' hnotbot hcent
  -- `Φ(Q) ≤ Z(Q)` holds in both cases: in the commutative case `Z(Q) = ⊤`
  have hfrattini : frattini ↥Q ≤ Subgroup.center ↥Q := by
    rcases hPart3 with h | h
    · exact h
    · haveI : IsMulCommutative ↥Q := h
      rw [Subgroup.center_eq_top]
      exact le_top
  refine ⟨hPQ, hQp, hfrattini, ?_⟩
  by_cases hab : IsMulCommutative ↥Q
  · exact Or.inl hab
  · -- non-abelian case: `Z(Q) = [Q,Q]` and `P` centralises `Z(Q)`
    right
    obtain ⟨q, hq, hQpq⟩ := hQp
    have hZ : (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.centralizer (P : Set A) :=
      center_map_le_centralizer P Q hQn hq hQpq hab hcent
    refine ⟨le_antisymm ?_ ?_, hZ⟩
    · -- `Z(Q) ≤ [Q,Q]`
      have h3 : Subgroup.centralizer (P : Set A) ⊓ Q ≤ ⁅Q, Q⁆ :=
        centralizer_inf_le_commutator P Q hQn hcop hPQ
      have h4 : (Subgroup.center ↥Q).map Q.subtype ≤ ⁅Q, Q⁆ :=
        (le_inf hZ (Subgroup.map_subtype_le (Subgroup.center ↥Q))).trans h3
      rw [← Subgroup.map_subtype_commutator Q] at h4
      exact (Subgroup.map_le_map_iff_of_injective Q.subtype_injective).mp h4
    · -- `[Q,Q] ≤ Z(Q)`: Burnside's basis theorem
      have h5 : ⁅Q, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype :=
        (Work.PGroup.commutator_le_frattiniIn hq Q hQpq).trans (Subgroup.map_mono hfrattini)
      rw [← Subgroup.map_subtype_commutator Q] at h5
      exact (Subgroup.map_le_map_iff_of_injective Q.subtype_injective).mp h5

end Work.NormalComplement.AppVII
