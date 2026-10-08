import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.HS.centralizer_eq_A_of_comm_C_A
import Submission.Work.Higman.HS.erad_mem_iff
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.powSub_normal
import Submission.Work.Higman.C4Cover.c4_branch_CP_A2
import Submission.Work.Higman.HS.htc_transport
import Submission.Work.Higman.H8.c4_card_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped commutatorElement

namespace Work.Higman.HS

variable {P : Type} [Group P] [Finite P]

/-! ## Elementary structural facts in the `C₄` setting

In the configuration of `Work.Higman.HS.hard_two_cover` (`A ⊴ P` abelian `ξ`-invariant,
`Ω₁(P) ≤ A`, `[P,P] = A`, every square of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)`,
`|A| = |Ω₁(P)|²`) together with `⁅C,A⁆ = A²` we record:

* `⁅A,⊤⁆ = A²` (so `A/A²` is the target of the commutator pairing on `P/A`);
* `Z(P) = A²`;
* `C² = A²`.
-/

/-- `A² ≠ ⊥` in the `C₄` setting. -/
theorem powSub_two_ne_bot_aux (h : IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    Work.Higman.powSub A 2 ≠ ⊥ := by
  intro hb
  have hc : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
  have h4 := h.omega1_card_ge_four
  omega

/-- **`⁅A,⊤⁆ = A²`** in the `C₄` setting. -/
theorem comm_A_top_eq_aux (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) :
    ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2 := by
  have hle := commutator_A_top_le (A := A) hAn
  have hinv := map_xi_commutator_A_top h hAxi
  rcases xi_inv_sub_dichotomy h hAab hAxi htop hA4 hle hinv with hb | h2 | h3
  · exfalso
    have h1 : (⁅C, A⁆ : Subgroup P) ≤ ⊥ := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl le_top).trans (le_of_eq hb)
    rw [hCAd] at h1
    exact powSub_two_ne_bot_aux h htop (le_bot_iff.mp h1)
  · exact h2
  · exact absurd h3 (comm_self_false h hNA)

/-- **`Z(P) = A²`** in the `C₄` setting. -/
theorem center_eq_powSub_two_aux (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) :
    Subgroup.center P = Work.Higman.powSub A 2 := by
  have hA : Work.Higman.IsXiAbelNormal h A := ⟨hAn, hAxi, hAab⟩
  have hZleA : Subgroup.center P ≤ A := Work.Higman.center_le_of_maximal h hA hmax
  have hA2leZ : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
    rw [htop]; exact h.omega1_le_center
  have hZinv : (Subgroup.center P).map (h.xi : MulAut P).toMonoidHom = Subgroup.center P := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨z, hz, rfl⟩
      exact Work.Higman.aut_mem_center (h.xi : MulAut P) hz
    · intro x hx
      exact ⟨(h.xi : MulAut P).symm x,
        Work.Higman.aut_mem_center (h.xi : MulAut P).symm hx, by simp⟩
  rcases xi_inv_sub_dichotomy h hAab hAxi htop hA4 hZleA hZinv with h1 | h2 | h3
  · exfalso
    exact powSub_two_ne_bot_aux h htop (le_bot_iff.mp (hA2leZ.trans (le_of_eq h1)))
  · exact h2
  · exfalso
    have hAZ : A ≤ Subgroup.center P := le_of_eq h3.symm
    have h1 : (⁅C, A⁆ : Subgroup P) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro c _
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_center_iff.mp (hAZ ha) c).symm
    rw [hCAd] at h1
    exact powSub_two_ne_bot_aux h htop h1

/-- `⁅C,C⁆ ≤ C²` for any subgroup `C` (from `⁅x,y⁆ = x² (x⁻¹y)² (y²)⁻¹`). -/
theorem commutator_le_powSub_two (C : Subgroup P) : ⁅C, C⁆ ≤ Work.Higman.powSub C 2 := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have key : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y ^ 2)⁻¹ := by
    rw [commutatorElement_def, pow_two (a := x), pow_two (a := x⁻¹ * y), pow_two (a := y)]
    group
  rw [key]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Work.Higman.pow_mem_powSub hx)
    (Work.Higman.pow_mem_powSub (C.mul_mem (C.inv_mem hx) hy)))
    (Subgroup.inv_mem _ (Work.Higman.pow_mem_powSub hy))

/-- The commutator-square identity `⁅x²,y⁆ = ⁅x,⁅x,y⁆⁆ ⁅x,y⁆²`. -/
theorem commutatorElement_sq_self (x y : P) :
    ⁅x ^ 2, y⁆ = ⁅x, ⁅x, y⁆⁆ * ⁅x, y⁆ ^ 2 := by
  simp only [commutatorElement_def, pow_two]
  group

/-- **`C² = A²`** in the `C₄` setting: `C² ≤ A`, `C² ∈ {⊥, A², A}`, and neither `⊥` nor `A`
can occur. -/
theorem powSub_C_eq_powSub_A_two (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    Work.Higman.powSub C 2 = Work.Higman.powSub A 2 := by
  have hC2inv : (Work.Higman.powSub C 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub C 2 := Work.Higman.map_powSub (h.xi : MulAut P) hCinv 2
  rcases xi_inv_sub_dichotomy h hAab hAxi htop hA4 hC2 hC2inv with hb | h2 | h3
  · -- `C² = ⊥` contradicts `[C,C] = A²`
    exfalso
    have h1 : ⁅C, C⁆ ≤ (⊥ : Subgroup P) := (commutator_le_powSub_two C).trans (le_of_eq hb)
    rw [hCd] at h1
    exact powSub_two_ne_bot_aux h htop (le_bot_iff.mp h1)
  · exact h2
  · -- `C² = A`: then `⁅x²,y⁆ = 1` for `x y ∈ C` since `⁅x,y⁆ ∈ A² = Ω₁(P)` is central of
    -- order two, whence `A = C²` centralises `C`, contradicting `⁅C,A⁆ = A²`
    exfalso
    have hA2Z : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
      rw [htop]; exact h.omega1_le_center
    have hA2inv : ∀ z ∈ Work.Higman.powSub A 2, z ^ 2 = 1 := by
      intro z hz
      exact h.mem_omega1.mp (htop ▸ hz)
    have key : ∀ x y : P, x ∈ C → y ∈ C → ⁅x ^ 2, y⁆ = 1 := by
      intro x y hx hy
      have hxy : ⁅x, y⁆ ∈ Work.Higman.powSub A 2 := by
        rw [← hCd]
        exact Subgroup.commutator_mem_commutator hx hy
      have hcen : ⁅x, y⁆ ∈ Subgroup.center P := hA2Z hxy
      have h2 : ⁅x, ⁅x, y⁆⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hcen x)
      rw [commutatorElement_sq_self, h2, hA2inv _ hxy, one_mul]
    have hcent : A ≤ Subgroup.centralizer (C : Set P) := by
      rw [← h3, Work.Higman.powSub, Subgroup.closure_le]
      rintro z ⟨x, hx, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      exact (commutatorElement_eq_one_iff_mul_comm.mp (key x y hx hy)).symm
    have hbot : (⁅A, C⁆ : Subgroup P) = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hz : Work.Higman.powSub A 2 = ⊥ := by
      rw [← hCAd, Subgroup.commutator_comm]
      exact hbot
    exact powSub_two_ne_bot_aux h htop hz

/-! ## The subgroup `E = {x : ⁅x,y⁆ ∈ A² for all y}`

This is the preimage of the centre of `P ⧸ A²`; it is the radical of the commutator pairing
`P/A × P/A → A/A²` and is the key auxiliary object for the surviving case `⁅C,⊤⁆ = A`
(see `Submission/Work/Higman/HS/NOTES_hard_two_cover.md`).
-/

/-- `{x : ⁅x,y⁆ ∈ A² for all y}`, the preimage of the centre of `P ⧸ A²`. -/
noncomputable def Erad (h : IsSuzuki2Grp P) (A : Subgroup P) [hAn : A.Normal] : Subgroup P :=
  letI : (Work.Higman.powSub A 2).Normal := Work.Higman.powSub_normal hAn 2
  Subgroup.comap (QuotientGroup.mk' (Work.Higman.powSub A 2))
    (Subgroup.center (P ⧸ (Work.Higman.powSub A 2)))

/-- `x` lies in `Erad h A` iff all its commutators with `P` lie in `A²`. -/
theorem mem_Erad_iff {h : IsSuzuki2Grp P} {A : Subgroup P} [hAn : A.Normal] {x : P} :
    x ∈ Erad h A ↔ ∀ y : P, x * y * x⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2 := by
  haveI := Work.Higman.powSub_normal hAn 2
  unfold Erad
  exact erad_mem_iff

/-- `Erad h A` is a normal subgroup. -/
theorem Erad_normal {h : IsSuzuki2Grp P} {A : Subgroup P} [hAn : A.Normal] :
    (Erad h A).Normal := by
  haveI := Work.Higman.powSub_normal hAn 2
  unfold Erad
  exact Subgroup.Normal.comap inferInstance (QuotientGroup.mk' (Work.Higman.powSub A 2))

/-- `A ≤ Erad h A` whenever `⁅A,⊤⁆ = A²`. -/
theorem A_le_Erad {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) : A ≤ Erad h A := by
  have h1 : ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2 :=
    comm_A_top_eq_aux h hAab hAxi hNA htop hA4 hCAd
  intro a ha
  rw [mem_Erad_iff]
  intro y
  have h2 : ⁅a, y⁆ ∈ ⁅A, (⊤ : Subgroup P)⁆ :=
    Subgroup.commutator_mem_commutator ha (Subgroup.mem_top y)
  rw [h1] at h2
  simpa [commutatorElement_def] using h2

/-- `Erad h A` is `ξ`-invariant. -/
theorem map_xi_Erad {h : IsSuzuki2Grp P} {A : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A) :
    (Erad h A).map (h.xi : MulAut P).toMonoidHom = Erad h A := by
  have hA2inv : (Work.Higman.powSub A 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub A 2 := Work.Higman.map_powSub (h.xi : MulAut P) hAxi 2
  have key : ∀ x : P, h.xi x ∈ Erad h A ↔ x ∈ Erad h A := by
    intro x
    rw [mem_Erad_iff, mem_Erad_iff]
    constructor
    · intro hx y
      have h1 : h.xi (x * y * x⁻¹ * y⁻¹) ∈ Work.Higman.powSub A 2 := by
        have h2 := hx (h.xi y)
        rw [show h.xi (x * y * x⁻¹ * y⁻¹)
            = h.xi x * h.xi y * (h.xi x)⁻¹ * (h.xi y)⁻¹ by
              rw [map_mul, map_mul, map_mul, map_inv, map_inv]]
        exact h2
      have h3 := Work.Higman.symm_mem_of_map_eq (h.xi : MulAut P) hA2inv h1
      simpa using h3
    · intro hx y
      have h1 : x * (h.xi : MulAut P).symm y * x⁻¹ * ((h.xi : MulAut P).symm y)⁻¹
          ∈ Work.Higman.powSub A 2 := hx _
      have h2 : h.xi (x * (h.xi : MulAut P).symm y * x⁻¹ * ((h.xi : MulAut P).symm y)⁻¹)
          ∈ (Work.Higman.powSub A 2).map (h.xi : MulAut P).toMonoidHom :=
        Subgroup.mem_map_of_mem _ h1
      rw [hA2inv] at h2
      rw [show h.xi (x * (h.xi : MulAut P).symm y * x⁻¹ * ((h.xi : MulAut P).symm y)⁻¹)
          = h.xi x * y * (h.xi x)⁻¹ * y⁻¹ by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv]
            simp] at h2
      exact h2
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact (key y).mpr hy
  · intro x hx
    refine ⟨(h.xi : MulAut P).symm x, (key _).mp ?_, by simp⟩
    simpa using hx

/-! ## The dichotomy for `⁅C,⊤⁆` -/

/-- In the `C₄` setting, `⁅C,⊤⁆` lies between `[C,C] = A²` and `[⊤,⊤] = A`, so it is `A²` or
`A`. -/
theorem comm_C_top_dichotomy (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    ⁅C, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2 ∨
      ⁅C, (⊤ : Subgroup P)⁆ = A := by
  have hle : (⁅C, (⊤ : Subgroup P)⁆ : Subgroup P) ≤ A := by
    calc ⁅C, (⊤ : Subgroup P)⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ :=
          Subgroup.commutator_mono le_top le_rfl
      _ = A := hGs
  have hinv : (⁅C, (⊤ : Subgroup P)⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom
      = ⁅C, (⊤ : Subgroup P)⁆ := by
    rw [Subgroup.map_commutator, hCinv,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]
  rcases xi_inv_sub_dichotomy h hAab hAxi htop hA4 hle hinv with hb | h2 | h3
  · exfalso
    have hb2 : (⁅C, C⁆ : Subgroup P) ≤ (⊥ : Subgroup P) :=
      (Subgroup.commutator_mono le_rfl le_top).trans (le_of_eq hb)
    rw [hCd] at hb2
    exact powSub_two_ne_bot_aux h htop (le_bot_iff.mp hb2)
  · exact Or.inl h2
  · exact Or.inr h3

/-- In the `C₄` setting with `⁅C,⊤⁆ = A`, a `ξ`-invariant normal subgroup `A < E` that
centralises `P` modulo `A²` cannot be contained in `C`. -/
theorem Erad_not_le_C_of_gt (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCTop : ⁅C, (⊤ : Subgroup P)⁆ = A)
    (hEgt : A < Erad h A) :
    ¬ (Erad h A ≤ C) := by
  intro hEC
  have hAne2 : A ≠ Work.Higman.powSub A 2 := by
    intro heq
    rw [heq, htop] at hcard
    have h4 := h.omega1_card_ge_four
    have hp : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
    nlinarith [hcard, h4, hp]
  have hAEr : A ≤ Erad h A := A_le_Erad (h := h) hAab hAxi hNA htop hA4 hCAd
  have hErn : (Erad h A).Normal := Erad_normal
  have hErinv : (Erad h A).map (h.xi : MulAut P).toMonoidHom = Erad h A := map_xi_Erad hAxi
  rcases hcover (Erad h A) hErn hErinv hAEr hEC with h1 | h1
  · exact absurd h1.symm (ne_of_lt hEgt)
  · have hle : (⁅C, (⊤ : Subgroup P)⁆ : Subgroup P) ≤ Work.Higman.powSub A 2 := by
      rw [Subgroup.commutator_le]
      intro c hc y _
      have hc' : c ∈ Erad h A := by rw [h1]; exact hc
      rw [mem_Erad_iff] at hc'
      simpa [commutatorElement_def] using hc' y
    rw [hCTop] at hle
    exact hAne2 (le_antisymm hle (Work.Higman.powSub_le (by norm_num)))

/-! ## The elementary quotient lemma closing the case `A < Erad h A`

The bundled hypothesis package `HardTwoCoverData`, the descent step
`Work.Higman.HS.htc_hard_two_cover_descent`, and the subgroup-transport lemmas it needs live in
`Submission/Work/Higman/HS/htc_transport.lean` (this module imports it).

If `P = C ⊔ E` with `⁅C,C⁆ ≤ A²` and `E ≤ Erad h A` (i.e. `E` centralises `P` modulo `A²`),
then the whole commutator subgroup of `P` lies in `A²`.  The computation is carried out
elementwise, using the two elementary identities
`⁅x * y, z⁆ = x * ⁅y,z⁆ * x⁻¹ * ⁅x,z⁆` and `⁅x, y*z⁆ = ⁅x,y⁆ * y * ⁅x,z⁆ * y⁻¹`
together with the normality of `A²`. -/

/-- **`P = C ⊔ E`, `⁅C,C⁆ ≤ A²`, `E ≤ Erad h A` ⟹ `⁅⊤,⊤⁆ ≤ A²`.** -/
theorem commutator_le_powSub_two_of_sup (h : IsSuzuki2Grp P) {A C E : Subgroup P} [hAn : A.Normal]
    [hCn : C.Normal] (hCE : C ⊔ E = ⊤)
    (hCC : ⁅C, C⁆ ≤ Work.Higman.powSub A 2) (hE : E ≤ Erad h A) :
    ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ Work.Higman.powSub A 2 := by
  haveI hNn : (Work.Higman.powSub A 2).Normal := Work.Higman.powSub_normal hAn 2
  rw [← hCE, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨c, hc, e, he, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := C) (t := E)).mp hx
  obtain ⟨c', hc', e', he', rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := C) (t := E)).mp hy
  have hEcomm : ∀ u ∈ E, ∀ y : P, ⁅u, y⁆ ∈ Work.Higman.powSub A 2 := by
    intro u hu y
    have h1 := (mem_Erad_iff.mp (hE hu)) y
    simpa [commutatorElement_def] using h1
  have hkey : ∀ x y z : P, ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    intro x y z; rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
  have hkey2 : ∀ x y z : P, ⁅x, y * z⁆ = ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ := by
    intro x y z; rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
  have h5 : ⁅e, c' * e'⁆ ∈ Work.Higman.powSub A 2 := by
    rw [hkey2 e c' e']
    rw [show ⁅e, c'⁆ * c' * ⁅e, e'⁆ * c'⁻¹ = ⁅e, c'⁆ * (c' * ⁅e, e'⁆ * c'⁻¹) by group]
    exact (Work.Higman.powSub A 2).mul_mem (hEcomm e he c')
      (hNn.conj_mem _ (hEcomm e he e') c')
  have h6 : ⁅c, c' * e'⁆ ∈ Work.Higman.powSub A 2 := by
    have hce' : ⁅c, e'⁆ ∈ Work.Higman.powSub A 2 := by
      have hh := hEcomm e' he' c
      rw [← commutatorElement_inv] at hh
      simpa using (Work.Higman.powSub A 2).inv_mem hh
    rw [hkey2 c c' e']
    rw [show ⁅c, c'⁆ * c' * ⁅c, e'⁆ * c'⁻¹ = ⁅c, c'⁆ * (c' * ⁅c, e'⁆ * c'⁻¹) by group]
    exact (Work.Higman.powSub A 2).mul_mem
      (hCC (Subgroup.commutator_mem_commutator hc hc')) (hNn.conj_mem _ hce' c')
  rw [hkey c e (c' * e')]
  exact (Work.Higman.powSub A 2).mul_mem (hNn.conj_mem _ h5 c) h6

/-- `A ≠ A²` in the `C₄` setting (`|A| = |Ω₁(P)|²`, `A² = Ω₁(P)`, `|Ω₁(P)| ≥ 4`). -/
theorem ne_powSub_two_of_card (h : IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    A ≠ Work.Higman.powSub A 2 := by
  intro heq
  have h3 : Nat.card ↥(Work.Higman.omega1 P) = Nat.card ↥A := by rw [← htop, ← heq]
  have hq : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 :=
    h3.trans hcard
  have h4 := h.omega1_card_ge_four
  have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
  nlinarith [hq, h4, hpos]

/-! ## `Erad h A = A` is *forced* in the case `⁅C,⊤⁆ = A`

This is the observation that pins the residual branch below: in the situation `M = ⊤`,
`⁅C,⊤⁆ = A` the radical `Erad h A` cannot properly contain `A`, so `Erad h A = A` is a
*consequence* of the data, not an extra hypothesis.  (`A ≤ Erad h A` is `A_le_Erad`.)  The
standalone statement of the residual in `Submission/Work/Higman/HS/…` therefore says the same
thing as the version without the `Erad = A` hypothesis.

Concretely: `A < Erad h A` gives `Erad h A ≰ C` (`Erad_not_le_C_of_gt`), so `C ⊔ Erad h A`
is a strictly larger `ξ`-invariant normal subgroup than `C`, hence `= ⊤` by `hMcover`; then
`commutator_le_powSub_two_of_sup` gives `⁅⊤,⊤⁆ ≤ A²`, i.e. `A = A²`, contradicting
`|A| = |Ω₁(P)|²` (`ne_powSub_two_of_card`). -/

/-- In the residual setting (`M = ⊤`, `⁅C,⊤⁆ = A`), `Erad h A` does not properly contain `A`. -/
theorem not_lt_Erad (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hMcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      C ≤ D → D = C ∨ D = ⊤)
    (hCTop : ⁅C, (⊤ : Subgroup P)⁆ = A) :
    ¬ (A < Erad h A) := by
  intro hgt
  have hnotle : ¬ Erad h A ≤ C :=
    Erad_not_le_C_of_gt h hAab hAxi hNA htop hA4 hcard hCAd hcover hCTop hgt
  haveI : C.Normal := hCn
  have hEn : (Erad h A).Normal := Erad_normal
  have hEinv : (Erad h A).map (h.xi : MulAut P).toMonoidHom = Erad h A := map_xi_Erad hAxi
  have hsupinv : (C ⊔ Erad h A).map (h.xi : MulAut P).toMonoidHom = C ⊔ Erad h A := by
    rw [Subgroup.map_sup, hCinv, hEinv]
  rcases hMcover (C ⊔ Erad h A) inferInstance hsupinv le_sup_left with hsup | hsup
  · exact hnotle ((le_sup_right : Erad h A ≤ C ⊔ Erad h A).trans (le_of_eq hsup))
  · have hcc : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ Work.Higman.powSub A 2 :=
      commutator_le_powSub_two_of_sup h hsup (le_of_eq hCd) le_rfl
    rw [hGs] at hcc
    exact ne_powSub_two_of_card h htop hcard
      (le_antisymm hcc (Work.Higman.powSub_le (by norm_num)))

/-- **The residual's `Erad h A = A` is not an extra hypothesis.**  Composing
`not_lt_Erad` with `A ≤ Erad h A` (`A_le_Erad`) shows that it is *derived* from the rest of
the residual data.  Consequently the frozen standalone target
`Higman/HS/c4_residual` (which does *not* carry `Erad h A = A` as a hypothesis) is exactly
this branch, and is the sharpest form of it. -/
theorem Erad_eq_A (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hMcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      C ≤ D → D = C ∨ D = ⊤)
    (hCTop : ⁅C, (⊤ : Subgroup P)⁆ = A) :
    Erad h A = A := by
  have hAEr : A ≤ Erad h A := A_le_Erad (h := h) hAab hAxi hNA htop hA4 hCAd
  refine le_antisymm ?_ hAEr
  by_contra hcon
  exact not_lt_Erad h hAab hAxi hNA hGs htop hA4 hcard hCn hCinv hcover hCAd hCd hMcover
    hCTop (lt_of_le_of_ne hAEr (fun heq => hcon (le_of_eq heq.symm)))

/-! ## The main theorem

The proof is by strong induction on `Nat.card P` over all instances of the bundled data.

* If `M < ⊤` the descent `htc_hard_two_cover_descent` transports the data to the Suzuki
  2-group `↥M` (of smaller order) and the induction hypothesis applies.
* If `M = ⊤`, the dichotomy `comm_C_top_dichotomy` gives `⁅C,⊤⁆ ∈ {A², A}`.  The case
  `⁅C,⊤⁆ = A²` is `C4Cover.c4_branch_CP_A2`; in the case `⁅C,⊤⁆ = A` the subgroup
  `E := Erad h A` satisfies `A ≤ E ⊴ P` and is `ξ`-invariant, and if `E > A` then
  `E ≰ C`, whence `C ⊔ E = ⊤` by `hMcover` and `commutator_le_powSub_two_of_sup` forces
  `A ≤ A²`, contradicting `|A| = |Ω₁(P)|²`.
* The residual case `E = A` is the `C₄` gap (Higman's Theorem 1 / Lemma 13 in the reducible
  case); it is isolated as the last `sorry` below. -/

theorem hard_two_cover {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C M : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A) (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hMn : M.Normal) (hMinv : M.map (h.xi : MulAut P).toMonoidHom = M)
    (hCM : C ≤ M) (hCMne : C ≠ M)
    (hMcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      C ≤ D → D ≤ M → D = C ∨ D = M)
    (hMd : ⁅M, M⁆ = A) : False := by
  classical
  -- Strong induction on `Nat.card` over all instances of the bundled data.
  have key : ∀ n : ℕ, ∀ (Q : Type) [Group Q] [Finite Q] (hQ : Work.Higman.IsSuzuki2Grp Q)
      (A' C' M' : Subgroup Q) [A'.Normal],
      Nat.card Q = n → HardTwoCoverData hQ A' C' M' → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Q hGQ hFQ hQ A' C' M' hAnQ hcardQ hd
      by_cases hMtop : M' = ⊤
      · -- ## `M = ⊤`: the dichotomy for `⁅C,⊤⁆`
        subst hMtop
        obtain ⟨hAxi, hAab, hmax, hNA, hGs, hsq, hA4, htop, hcard, hCn, hCinv, hAC, hCA,
          hcover, hC2, hCAd, hCd, hMn, hMinv, hCM, hCMne, hMcover, hMd⟩ := hd
        haveI : Subgroup.Normal C' := hCn
        have hcent : Subgroup.centralizer (A' : Set Q) = A' :=
          centralizer_eq_A_of_comm_C_A hQ hAxi hAab hNA hGs hsq hA4 htop hcard hCn hCinv
            hAC hcover hCAd
        rcases comm_C_top_dichotomy hQ hAab hAxi htop hA4 hGs hCinv hCd with hCT | hCT
        · exact C4Cover.c4_branch_CP_A2 hQ hAnQ hAab hGs hsq hA4 htop hcard hcent hCn hCinv
            hAC hCA hCT
        · -- ## `⁅C,⊤⁆ = A`: the radical `E := Erad h A`
          set E : Subgroup Q := Erad hQ A' with hEdef
          have hAEr : A' ≤ E := A_le_Erad (h := hQ) hAab hAxi hNA htop hA4 hCAd
          have hEn : Subgroup.Normal E := Erad_normal
          have hEinv : E.map (hQ.xi : MulAut Q).toMonoidHom = E := map_xi_Erad hAxi
          by_cases hEeq : E = A'
          · -- the residual `C₄` gap (`E = A`): this is exactly the configuration of
            -- `Work.Higman.H8.c4_gap_hard_false`
            have hC2eq : Work.Higman.powSub C' 2 = Work.Higman.powSub A' 2 :=
              powSub_C_eq_powSub_A_two hQ hAab hAxi htop hA4 hC2 hCinv hCAd hCd
            exact Work.Higman.H8.c4_gap_hard_false hQ ⟨hAnQ, hAxi, hAab⟩ hmax hNA hGs hsq hA4
              htop hcard hCn hCinv hAC hCA hcover hC2eq hCd hCAd hcent hCT
          · -- ## `A < E`: then `C ⊔ E = ⊤`, so `⁅⊤,⊤⁆ ≤ A²`
            have hEgt : A' < E := lt_of_le_of_ne hAEr (Ne.symm hEeq)
            have hnotle : ¬ E ≤ C' :=
              Erad_not_le_C_of_gt hQ hAab hAxi hNA htop hA4 hcard hCAd hcover hCT hEgt
            haveI : Subgroup.Normal (C' ⊔ E) := inferInstance
            have hsupinv : (C' ⊔ E).map (hQ.xi : MulAut Q).toMonoidHom = C' ⊔ E := by
              rw [Subgroup.map_sup, hCinv, hEinv]
            rcases hMcover (C' ⊔ E) inferInstance hsupinv le_sup_left le_top with hsup | hsup
            · exact hnotle ((le_sup_right : E ≤ C' ⊔ E).trans (le_of_eq hsup))
            · have hcc : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Work.Higman.powSub A' 2 :=
                commutator_le_powSub_two_of_sup hQ hsup (le_of_eq hCd) (le_of_eq hEdef)
              rw [hGs] at hcc
              exact ne_powSub_two_of_card hQ htop hcard
                (le_antisymm hcc (Work.Higman.powSub_le (by norm_num)))
      · -- ## `M < ⊤`: descend to the Suzuki 2-group `↥M`
        exact htc_hard_two_cover_descent hQ hd (lt_of_le_of_ne le_top hMtop)
          (fun Q' hGQ' hFQ' hQ' A'' C'' M'' hAnQ' hlt hd' =>
            ih (Nat.card Q') (by rw [← hcardQ]; exact hlt) Q' hQ' A'' C'' M'' rfl hd')
  exact key (Nat.card P) P h A C M rfl
    ⟨hAxi, hAab, hmax, hNA, hGs, hsq, hA4, htop, hcard, hCn, hCinv, hAC, hCA, hcover,
      hC2, hCAd, hCd, hMn, hMinv, hCM, hCMne, hMcover, hMd⟩

/-- `hard_two_cover` from the bundled data. -/
theorem hard_two_cover_of_data {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C M : Subgroup P} [hAn : A.Normal] (hd : HardTwoCoverData h A C M) : False := by
  obtain ⟨hAxi, hAab, hmax, hNA, hGs, hsq, hA4, htop, hcard, hCn, hCinv, hAC, hCA, hcover,
    hC2, hCAd, hCd, hMn, hMinv, hCM, hCMne, hMcover, hMd⟩ := hd
  exact hard_two_cover h hAxi hAab hmax hNA hGs hsq hA4 htop hcard hCn hCinv hAC hCA hcover
    hC2 hCAd hCd hMn hMinv hCM hCMne hMcover hMd

end Work.Higman.HS
