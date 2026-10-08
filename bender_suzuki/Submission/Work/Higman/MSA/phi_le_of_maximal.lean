import Mathlib
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.endgame
import Submission.Work.Higman.MSA.higman_lemma7_msa
import Submission.Work.Higman.MSA.commutator_le_center_of_unique_abelian_char
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.equivariant_bihom_trivial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.MSA

variable {P : Type} [Group P] [Finite P]

/-- `powSub A n` is normal whenever `A` is (conjugation commutes with the `n`-th power map). -/
theorem powSub_normal_of_normal {A : Subgroup P} (hA : A.Normal) (n : ℕ) :
    (powSub A n).Normal := by
  refine Subgroup.Normal.mk (fun x hx g => ?_)
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have hconj : (g * a * g⁻¹) ^ n = g * a ^ n * g⁻¹ := by
        induction n with
        | zero => simp
        | succ k ih => rw [pow_succ, pow_succ, ih]; group
      rw [← hconj]
      exact pow_mem_powSub (hA.conj_mem a ha g)
  | one => simp
  | mul a b _ _ iha ihb =>
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ iha

/-- **Higman 1963, Lemma 9, second part (Higman §5 endgame).**  If `A` is a maximal
`ξ`-invariant abelian normal subgroup of a Suzuki 2-group `P` with `powSub A 4 = ⊥`, then
`Φ(P) = powSub ⊤ 2 ⊔ ⁅⊤,⊤⁆ ≤ A`, i.e. `[P,P] ≤ A` and every square of `P` lies in `A`.

PROOF (Higman §5, endgame; full discussion in `Submission/Work/Higman/MSA_NOTES.md` §4).

Assume `Φ(P) ≰ A` and put `Φ := powSub ⊤ 2 ⊔ ⁅⊤,⊤⁆ = Φ(P)`.  By
`commutator_frattini_centralizes`, `Φ ≤ C_P(A)`, and `M := A ⊔ Φ` is a `ξ`-invariant normal
subgroup properly containing `A` (`A ≤ C_P(A)` as `A` is abelian).  By `exists_minimal_covering`
there is a minimal covering `A < C ≤ M`; then `C ≤ C_P(A)` as well, i.e. `[C,A] = 1`.

`Φ(C) = powSub C 2 ⊔ ⁅C,C⁆ ≤ A` (`phi_le_of_minimal_covering`) and `A² ≤ Φ(C)` (as `A ≤ C`), so
`Φ(C) ∈ {A², A}` by `xi_invariant_eq_powSub_two_or_self`.

* `Φ(C) = A²`: pick `c ∈ C∖A`; then `c² ∈ C² ⊆ A²` and `[c,A] ⊆ [C,A] = 1`, so Higman's Lemma 2
  (`higman_lemma2`) contradicts `c² ∈ A²` and `[c,A] ⊆ A⁴`.

* `Φ(C) = A`: then `C² ≤ A`, `C' = ⁅C,C⁆ ≤ A`, and `C' = powSub A (2^j)` for some `j`
  (`homogeneous_structure`).
  - `j ≥ 1` (i.e. `C' ≤ A²`): Higman's Lemma 7 — here the proved lemma
    `Work.Higman.MSA.higman_lemma7_msa` — makes `C` abelian, contradicting `hmax`.
  - `j = 0` (i.e. `C' = A`): for `c d ∈ C` one has `⁅c,d⁆ ∈ C' = A`, and `A ≤ Z(C)`, so the
    class-two identity gives `⁅c²,d⁆ = ⁅c,d⁆²`; as `c² ∈ C² ⊆ A` also `⁅c²,d⁆ = 1`, so every
    commutator of `C` is an involution and `A = C' ≤ Ω₁(P) ≤ A`, i.e. `A = Ω₁(P)`.
    Hence `Z(P) = A` (`center_le_of_maximal`) and every abelian characteristic subgroup of `P`
    is `⊥` or `Z(P)`: if `B` is abelian and characteristic then `A ⊔ B` is `ξ`-invariant abelian
    normal (`A = Z(P)` is central), so `A ⊔ B = A` by maximality, `B ≤ A = Ω₁(P)`, and `B` is a
    `ξ`-invariant subgroup of `Ω₁(P)`, hence `⊥` or `Ω₁(P)` by irreducibility of `Ω₁(P)` under
    `ξ`.  The lemma `commutator_le_center_of_unique_abelian_char` now gives `P' ≤ Z(P) = A`, and
    then `[x²,y] = [x,y]² = 1` for all `x,y` (as `[x,y] ∈ Z(P) = Ω₁(P)`), i.e. `x² ∈ Z(P) = A`.
    So `Φ(P) ≤ A` after all, contradicting the assumption. -/
theorem phi_le_of_maximal {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (h4 : Work.Higman.powSub A 4 = ⊥) :
    Work.Higman.powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hOm : omega1 P ≤ A := omega1_le_of_maximal h hA hmax
  have hAne : A ≠ ⊥ := by
    intro hbot
    obtain ⟨x, y, hx2, hy2, hxy⟩ := h.manyInvol
    have hx : x ∈ omega1 P := h.mem_omega1.mpr (by rw [← orderOf_dvd_iff_pow_eq_one, hx2])
    have hxA : x ∈ A := hOm hx
    rw [hbot] at hxA
    have hx1 : x = 1 := by simpa using hxA
    rw [hx1] at hx2
    exact absurd hx2 (by norm_num)
  -- the Frattini subgroup, as a subgroup of `P`
  set Φ : Subgroup P := powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ with hΦdef
  have hconΦ : ¬ (Φ ≤ A) := by rw [hΦdef]; exact hcon
  haveI hAn : A.Normal := hA.normal
  haveI hpowN : (powSub (⊤ : Subgroup P) 2).Normal := powSub_normal_of_normal Subgroup.normal_top 2
  haveI hcomN : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).Normal :=
    Subgroup.commutator_normal _ _
  haveI hΦn : Φ.Normal := by rw [hΦdef]; exact Subgroup.sup_normal _ _
  have hΦinv : Φ.map (h.xi : MulAut P).toMonoidHom = Φ := by
    rw [hΦdef, Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective,
      map_powSub (h.xi : MulAut P)
        (Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective) 2]
  haveI hMn : (A ⊔ Φ).Normal := Subgroup.sup_normal A Φ
  have hMinv : (A ⊔ Φ).map (h.xi : MulAut P).toMonoidHom = A ⊔ Φ := by
    rw [Subgroup.map_sup, hA.map_eq, hΦinv]
  have hMA : A ⊔ Φ ≠ A := fun hEq => hconΦ (hEq ▸ le_sup_right)
  obtain ⟨C, hCn, hCinv, hAC, hCM, hCA, hcover⟩ :=
    exists_minimal_covering h hMn hMinv le_sup_left hMA
  -- `C` centralizes `A`, because `A ≤ C_P(A)` and `Φ ≤ C_P(A)`
  have hAcen : A ≤ Subgroup.centralizer (A : Set P) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hA.abelian a ha b hb).symm
  have hCcen : C ≤ Subgroup.centralizer (A : Set P) :=
    hCM.trans (sup_le hAcen (commutator_frattini_centralizes hA h4))
  have hZA : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c := by
    intro c hc a ha
    exact (Subgroup.mem_centralizer_iff.mp (hCcen hc) a ha).symm
  -- `Φ(C) ≤ A`, and `A² ≤ Φ(C)`
  have hPhi_le : powSub C 2 ⊔ ⁅C, C⁆ ≤ A :=
    phi_le_of_minimal_covering h hA.normal hA.map_eq hCn hCinv hAC (Ne.symm hCA) hcover
  have hA2le : powSub A 2 ≤ powSub C 2 ⊔ ⁅C, C⁆ :=
    (powSub_mono (n := 2) hAC).trans le_sup_left
  have hPhiCinv : (powSub C 2 ⊔ ⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom
      = powSub C 2 ⊔ ⁅C, C⁆ := by
    rw [Subgroup.map_sup, map_powSub (h.xi : MulAut P) hCinv 2, Subgroup.map_commutator, hCinv]
  rcases xi_invariant_eq_powSub_two_or_self h hA hPhi_le hA2le hPhiCinv with hsq | hself
  · -- ## Case `Φ(C) = A²`
    exfalso
    obtain ⟨u, huC, huA⟩ : ∃ u ∈ C, u ∉ A := by
      by_contra hc
      have hCAle : C ≤ A := fun u hu => by
        by_contra huA
        exact absurd ⟨u, hu, huA⟩ hc
      exact hCA (le_antisymm hCAle hAC)
    have hu2 : u ^ 2 ∈ powSub A 2 := by
      have h1 : u ^ 2 ∈ powSub C 2 := pow_mem_powSub huC
      have h2 : powSub C 2 ≤ powSub A 2 := by rw [← hsq]; exact le_sup_left
      exact h2 h1
    have hcomm : ∀ a ∈ A, ⁅u, a⁆ ∈ powSub A 4 := by
      intro a ha
      have h1 : ⁅u, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZA u huC a ha)
      rw [h1, h4]
      exact Subgroup.mem_bot.mpr rfl
    exact higman_lemma2 h hA hOm hAne huA ⟨hu2, hcomm⟩
  · -- ## Case `Φ(C) = A`
    have hC2_le : powSub C 2 ≤ A := by rw [← hself]; exact le_sup_left
    have hCd_le : ⁅C, C⁆ ≤ A := by rw [← hself]; exact le_sup_right
    have hCdinv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨e, he1, he2, he3, hstruct⟩ := homogeneous_structure h hA.abelian hA.map_eq
    obtain ⟨j, hj⟩ := hstruct ⁅C, C⁆ hCd_le hCdinv
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- ## Sub-case `C' = A`
      have hCdA : ⁅C, C⁆ = A := by rw [hj, hj0, pow_zero, powSub_one_eq]
      -- every commutator of `C` is an involution
      have hCd_sq : ∀ c ∈ C, ∀ d ∈ C, ⁅c, d⁆ ^ 2 = 1 := by
        intro c hc d hd
        have hmem : ⁅c, d⁆ ∈ A := hCdA ▸ Subgroup.commutator_mem_commutator hc hd
        have hcen : c * ⁅c, d⁆ = ⁅c, d⁆ * c := hZA c hc ⁅c, d⁆ hmem
        have h1 : ⁅c ^ 2, d⁆ = ⁅c, d⁆ * ⁅c, d⁆ := by
          rw [show c ^ 2 = c * c from pow_two c, commutatorElement_mul_left_eq_conj_mul, hcen]
          group
        have hcs : c ^ 2 ∈ A := hC2_le (pow_mem_powSub hc)
        have h2 : ⁅c ^ 2, d⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr ((hZA d hd (c ^ 2) hcs).symm)
        rw [show ⁅c, d⁆ ^ 2 = ⁅c ^ 2, d⁆ from by rw [h1, pow_two], h2]
      have hOA : A ≤ omega1 P := by
        rw [← hCdA]
        refine Subgroup.commutator_le.mpr (fun c hc d hd => ?_)
        exact h.mem_omega1.mpr (hCd_sq c hc d hd)
      have hAeqOm : A = omega1 P := le_antisymm hOA hOm
      have hAcenter : A ≤ Subgroup.center P := hAeqOm ▸ h.omega1_le_center
      have hZeqA : Subgroup.center P = A :=
        le_antisymm (center_le_of_maximal h hA hmax) hAcenter
      -- every abelian characteristic subgroup of `P` is `⊥` or `Z(P)`
      have huniq : ∀ B : Subgroup P, B.Characteristic →
          (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → B = ⊥ ∨ B = Subgroup.center P := by
        intro B hBchar hBabel
        rcases eq_or_ne B ⊥ with hBbot | hBne
        · exact Or.inl hBbot
        · right
          have hBinv : B.map (h.xi : MulAut P).toMonoidHom = B :=
            Subgroup.characteristic_iff_map_eq.mp hBchar (h.xi : MulAut P)
          have hBn : B.Normal :=
            (Subgroup.normal_iff_map_conj_eq).mpr
              (fun g => Subgroup.characteristic_iff_map_eq.mp hBchar (MulAut.conj g))
          have hsup : IsXiAbelNormal h (A ⊔ B) := by
            haveI := hBn
            refine ⟨Subgroup.sup_normal A B, ?_, ?_⟩
            · rw [Subgroup.map_sup, hA.map_eq, hBinv]
            · rw [sup_comm]
              exact sup_comm_of_le_center hBabel hAcenter
          have hsupA : A ⊔ B = A := hmax (A ⊔ B) hsup le_sup_left
          have hBA : B ≤ A := by rw [← hsupA]; exact le_sup_right
          have hBleOm : B ≤ omega1 P := hAeqOm ▸ hBA
          rcases inf_omega1_eq_bot_or_top (A := ⊤) h (le_inf le_top hBleOm) hBinv with h | h
          · exact absurd h hBne
          · rw [h, top_inf_eq]
            exact hAeqOm.symm.trans hZeqA.symm
      -- class two
      have hcomm_center : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P :=
        commutator_le_center_of_unique_abelian_char h.isPGroup.isNilpotent huniq
      -- hence every square is central
      have hsq_center : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
        intro x
        rw [Subgroup.mem_center_iff]
        intro y
        have hxyc : ⁅x, y⁆ ∈ Subgroup.center P :=
          hcomm_center (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
        have hxy2 : ⁅x, y⁆ ^ 2 = 1 := by
          have hmem : ⁅x, y⁆ ∈ omega1 P := by rw [← hAeqOm, ← hZeqA]; exact hxyc
          exact h.mem_omega1.mp hmem
        have hkey : ⁅x ^ 2, y⁆ = 1 := by
          have h1 : ⁅x ^ 2, y⁆ = ⁅x, y⁆ * ⁅x, y⁆ := by
            rw [show x ^ 2 = x * x from pow_two x, commutatorElement_mul_left_eq_conj_mul,
              Subgroup.mem_center_iff.mp hxyc x]
            group
          rw [h1, ← pow_two, hxy2]
        exact (commutatorElement_eq_one_iff_mul_comm.mp hkey).symm
      have hsqA : ∀ x : P, x ^ 2 ∈ A := fun x => hZeqA ▸ hsq_center x
      refine hconΦ (sup_le ?_ ?_)
      · rw [powSub, Subgroup.closure_le]
        rintro y ⟨x, -, rfl⟩
        exact hsqA x
      · rw [← hZeqA]
        exact hcomm_center
    · -- ## Sub-case `C' ⊆ A²` (Higman's Lemma 7)
      have hCd2 : ⁅C, C⁆ ≤ powSub A 2 := by
        rw [hj]
        exact powSub_le_of_dvd hA.abelian (Nat.pow_dvd_pow 2 hjpos)
      have hab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
        higman_lemma7_msa h hA hCn hCinv hAC hCA.symm hcover hself hCd2
      exact absurd (hmax C ⟨hCn, hCinv, hab⟩ hAC) hCA

end Work.Higman.MSA
