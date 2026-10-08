import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.InvSetCountNormalFourB
import Submission.Work.CORE4.NotA7.A6EvenStructure
import Submission.Work.CORE4.NotA7.A6EvenCentralizer
import Submission.Work.CORE4.A7Fusion
import Submission.Work.CORE4.A7Normalize
import Submission.Work.CORE4.A7VnotCyclicAux
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7UMCard
import Submission.Work.CORE4.ElementaryAbelianRankTwo
import Submission.Work.CORE4.A4aAux.U_not_isMulCommutative
import Submission.Work.CORE4.A4aAux.sup_isMulCommutative
import Submission.Work.BSW.Cases.K4.ncard_involutions_coset_eq

namespace Work.CORE4.NotA7

open Work.GW2 Subgroup

open scoped commutatorElement

set_option linter.style.haveILetI false
set_option maxHeartbeats 16000000

-- **A6 (weak form)**: Bender p. 226, "Next we show that |J ∩ My| ≤ 21 for every involution
-- `y ∈ G − M`".  (`Work.CORE4.C15.A7CosetWeakProp I` in `NotA7Defs.lean`.)
-- Statement: from `Hyp9 G B C`, `IsA7Case C.D`, `A7Facts1 C.D`, `A7Facts2 B C.D`, `A7Mid B C.D`
-- (= `A7UData ∧ ¬ Case2InvNormal ∧ A7Facts5`) conclude `A7Facts6 C.D`, i.e.
-- `∀ y, orderOf y = 2 → y ∉ C.D.M → {x | orderOf x = 2 ∧ x * y⁻¹ ∈ C.D.M}.ncard ≤ 21`.
-- Route (Bender, with 1.4 = `I.toolkit.fus`): `J ∩ My = I_{M∩M^y}(y)·y`, and
-- `|F g ∩ I_M(y)| ≤ 1` for `g ∈ M` (if `f g, g ∈ I_M(y)` then `f ∈ F ∩ F^{gy} = 1`, `C.F_ti`).
-- Odd case: `|I_M(y)| ≤ |M ⊓ M^y : (M ⊓ M^y) ⊓ F| ≤ 21` by `A7UData`'s last conjunct.  This is
-- exactly `Work.CORE4.A7CosetOdd` in `Submission/Work/CORE4/A7Coset.lean` (proved there for the
-- strong hypotheses; it uses only the last conjunct of `A7Facts3`).
-- Even case: conjugate inside `M` (one class of involutions in `M`: `Case2Pre.oneClass` +
-- `I.layerOneInvClass`, via `CountSetup.M_eq_layerIn_sup` and `A7Facts2`'s `S ≤ E`) to make
-- `y ∈ C_G(t)`; then `AV ⊴ H` (`A7Facts2`, `A7UData`) lies in `M ⊓ M^y`, `A ⊓ Z(M ⊓ M^y) ⊇ F` is
-- `y`-normalized so `M ⊓ M^y ≤ C_M(A)`, `|C_M(A)| ≤ 108` (`C_M(A) = C_M(K)`, and an element of
-- order `3` of `A₇` inverted by an involution has centralizer of order `36`; the small `A₇`
-- computation can be done by `decide` in the concrete model as `A7S4` was, or via
-- `Submission/Work/CORE4/{A7CMtFourGroup,CoreA7OddCentralizer,A7Fusion,CardCentralizer*}`),
-- `V ∈ Syl₂(M ⊓ M^y)`, and `|C_{AV}(y)| = 6`, giving at most `108/6 = 18 ≤ 21` involutions.
-- The partially-done sibling `Submission/Work/CORE4/A7Coset.lean` (design statement, with
-- `A7CosetOdd`/`A7CosetEven`) should be consulted (import, do not modify).
-- IMPORTANT: import ONLY modules that do not declare clashing `Work.GW2.*` names:
-- `Submission.Work.CORE4.*`, `Submission.Work.FUS.*`, `Submission.Work.RED.*`,
-- `Submission.Work.Dihedral.Defs`, `Submission.OddOrder.*`.

variable {G : Type} [Group G] [Finite G]

/-! ## Step 0: the coset count is the `invSet` count

Bender 1.4: the involutions of the coset `My` correspond bijectively (via `h ↦ h * y`) to the
elements of `M ∩ M^y` inverted by `y`.  This is the same computation as
`Work.CORE4.ncard_coset_eq_invSet` in `Submission/Work/CORE4/A7Coset.lean`, reproved here so that
the file does not depend on that one (which still carries a `sorry` elsewhere). -/

/-- Membership in `conjSub y M` is being a conjugate `y * a * y⁻¹` of a member of `M`. -/
theorem mem_conjSub_iff_loc (M : Subgroup G) (y m : G) :
    m ∈ Work.GW2.conjSub y M ↔ ∃ a ∈ M, y * a * y⁻¹ = m := by
  rw [Work.GW2.conjSub]
  constructor
  · intro h
    rw [Subgroup.mem_map] at h
    obtain ⟨a, ha, haa⟩ := h
    exact ⟨a, ha, by rw [← haa]; rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_map]
    exact ⟨a, ha, rfl⟩

/-- The number of involutions in the coset `My` equals the number of elements of `M ∩ M^y`
inverted by `y` (Bender 1.4). -/
theorem ncard_coset_eq_invSet_loc (M : Subgroup G) (y : G) (hy : orderOf y = 2) (hyM : y ∉ M) :
    {x : G | orderOf x = 2 ∧ x * y⁻¹ ∈ M}.ncard =
      (Work.GW2.invSet (M ⊓ Work.GW2.conjSub y M) y).ncard := by
  classical
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy, pow_two] at h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  -- the target set is the set of involutions in the coset
  have hset : {x : G | orderOf x = 2 ∧ x * y⁻¹ ∈ M}
      = {x : G | orderOf x = 2 ∧ ∃ m ∈ M, x = m * y} := by
    ext x
    constructor
    · intro h
      exact ⟨h.1, x * y⁻¹, h.2, by rw [mul_assoc, inv_mul_cancel, mul_one]⟩
    · rintro ⟨h1, m, hm, rfl⟩
      exact ⟨h1, by rwa [mul_assoc, mul_inv_cancel, mul_one]⟩
  rw [hset]
  have hbs := Work.BSW.Cases.K4.ncard_involutions_coset_eq M y hy hyM
  have hfun : ({m : G | m ∈ M ∧ y * m * y = m⁻¹} : Set G)
      = (Work.GW2.invSet (M ⊓ Work.GW2.conjSub y M) y : Set G) := by
    ext m
    simp only [Work.GW2.invSet, Set.mem_setOf_eq, Subgroup.mem_inf]
    constructor
    · rintro ⟨hmM, hconj⟩
      have hconj' : y * m * y⁻¹ = m⁻¹ := by rw [hyinv]; exact hconj
      refine ⟨⟨hmM, ?_⟩, hconj'⟩
      show m ∈ Work.GW2.conjSub y M
      rw [Work.GW2.conjSub, Subgroup.mem_map]
      refine ⟨m⁻¹, M.inv_mem hmM, ?_⟩
      show y * m⁻¹ * y⁻¹ = m
      calc y * m⁻¹ * y⁻¹ = (y * m * y⁻¹)⁻¹ := by group
        _ = m := by rw [hconj']; simp
    · rintro ⟨⟨hmM, _⟩, hconj⟩
      exact ⟨hmM, by rw [hyinv] at hconj; exact hconj⟩
  rw [hbs, hfun]

/-- The `invSet` is contained in the subgroup. -/
theorem invSet_ncard_le_loc (M : Subgroup G) (y : G) :
    (Work.GW2.invSet M y).ncard ≤ Nat.card M := by
  classical
  have h : (Work.GW2.invSet M y : Set G) ⊆ (M : Set G) := fun x hx => hx.1
  calc (Work.GW2.invSet M y).ncard ≤ (M : Set G).ncard := Set.ncard_le_ncard h
    _ = Nat.card M := by
        rw [← Nat.card_coe_set_eq (s := (M : Set G))]
        exact rfl

/-! ## Step 1: the odd case

Bender's "As `2'`-subgroups of `M/F ≅ A₇` have order at most `21`" argument.  This is the proof
of `Work.CORE4.A7CosetOdd` with the hypothesis `A7Facts3` cut down to the `A7UData` conjunct
`∀ X ≤ D.M, Odd |X| → |X| ≤ 21 * |X ⊓ F|`. -/
theorem A7CosetOddWeak (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.CORE4.A7Mid B C.D →
          ∀ y : G, orderOf y = 2 → y ∉ C.D.M →
            Odd (Nat.card ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M)) →
              (Work.GW2.invSet (C.D.M ⊓ Work.GW2.conjSub y C.D.M) y).ncard ≤ 21 := by
  intro G _ _ B C _hHyp _hA7 h1 _h2 hMid y hy2 hyM hodd
  classical
  set N : Subgroup G := C.D.M ⊓ Work.GW2.conjSub y C.D.M with hN
  have hNM : N ≤ C.D.M := by rw [hN]; exact inf_le_left
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hmemN : ∀ n : G, n ∈ N ↔ n ∈ C.D.M ∧ ∃ a ∈ C.D.M, y * a * y⁻¹ = n := by
    intro n
    rw [hN]
    constructor
    · intro hn
      obtain ⟨hm, hc⟩ := Subgroup.mem_inf.mp hn
      exact ⟨hm, (mem_conjSub_iff_loc C.D.M y n).mp hc⟩
    · rintro ⟨hm, hc⟩
      exact Subgroup.mem_inf.mpr ⟨hm, (mem_conjSub_iff_loc C.D.M y n).mpr hc⟩
  have hstep : ∀ n : G, n ∈ N → y * n * y⁻¹ ∈ N := by
    intro n hn
    obtain ⟨hnM, a, haM, ha⟩ := (hmemN n).mp hn
    rw [hmemN]
    refine ⟨?_, n, hnM, by rfl⟩
    have heq : y * (y * a * y⁻¹) * y⁻¹ = a := by
      have h1' : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hyy, inv_one]
      calc y * (y * a * y⁻¹) * y⁻¹ = (y * y) * a * (y⁻¹ * y⁻¹) := by group
        _ = 1 * a * 1 := by rw [hyy, h1']
        _ = a := by simp
    rw [← ha, heq]
    exact haM
  have hnorm : y ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hstep n
    · intro hn
      have h2' := hstep (y * n * y⁻¹) hn
      have heq : y * (y * n * y⁻¹) * y⁻¹ = n := by
        have h1' : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hyy, inv_one]
        calc y * (y * n * y⁻¹) * y⁻¹ = (y * y) * n * (y⁻¹ * y⁻¹) := by group
          _ = 1 * n * 1 := by rw [hyy, h1']
          _ = n := by simp
      rwa [heq] at h2'
  obtain ⟨-, h15, -⟩ := I.toolkit.c15 G I.toolkit.ft N y hy2 hodd hnorm
  have h3N : Nat.card ↥N ≤ 21 * Nat.card ↥(N ⊓ C.D.F) := hMid.1.2.2.2 N hNM hodd
  by_cases hbot : N ⊓ C.D.F = ⊥
  · have hcard1 : Nat.card ↥(N ⊓ C.D.F) = 1 := by rw [hbot]; simp
    have hN21 : Nat.card ↥N ≤ 21 := by
      have h := h3N
      rw [hcard1, mul_one] at h
      exact h
    calc (Work.GW2.invSet N y).ncard ≤ Nat.card ↥N := invSet_ncard_le_loc N y
      _ ≤ 21 := hN21
  · have hF3 : Nat.card C.D.F = 3 := h1.2.1
    have hcard : Nat.card ↥(N ⊓ C.D.F) = 3 := by
      have hdvd : Nat.card ↥(N ⊓ C.D.F) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (inf_le_right : N ⊓ C.D.F ≤ C.D.F)
        rwa [hF3] at h
      have hne1 : Nat.card ↥(N ⊓ C.D.F) ≠ 1 := fun hone => hbot (Subgroup.card_eq_one.mp hone)
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hFN : N ⊓ C.D.F = C.D.F :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hF3, hcard])
    have hFle : C.D.F ≤ N :=
      (show C.D.F ≤ N ⊓ C.D.F by rw [hFN]).trans inf_le_left
    have hN63 : Nat.card ↥N ≤ 63 := by
      have h := h3N
      rw [hFN, hF3] at h
      omega
    have hCne : N ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥ := by
      intro hCbot
      have hcardC : Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) = 1 := by
        rw [hCbot]; simp
      have hIcard : (Work.GW2.invSet N y).ncard = Nat.card ↥N := by
        have h := h15
        rw [hcardC, mul_one] at h
        exact h
      have hsub : (Work.GW2.invSet N y : Set G) ⊆ (N : Set G) := fun x hx => hx.1
      have hset : (Work.GW2.invSet N y : Set G) = (N : Set G) := by
        refine Set.eq_of_subset_of_ncard_le hsub ?_
        have h1' : (N : Set G).ncard = Nat.card ↥N := by
          rw [← Nat.card_coe_set_eq (s := (N : Set G))]
          exact rfl
        rw [h1', hIcard]
      have hstepF : ∀ x : G, x ∈ C.D.F → y * x * y⁻¹ ∈ C.D.F := by
        intro x hx
        have hxN : x ∈ N := hFle hx
        have hxI : x ∈ Work.GW2.invSet N y := by rw [hset]; exact hxN
        rw [hxI.2]
        exact C.D.F.inv_mem hx
      have hnormF : y ∈ Subgroup.normalizer (C.D.F : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact hstepF x
        · intro hx
          have h2' := hstepF (y * x * y⁻¹) hx
          have heq : y * (y * x * y⁻¹) * y⁻¹ = x := by
            have h1' : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hyy, inv_one]
            calc y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y⁻¹ * y⁻¹) := by group
              _ = 1 * x * 1 := by rw [hyy, h1']
              _ = x := by simp
          rwa [heq] at h2'
      have hyM' : y ∈ C.D.M := by
        rw [Work.GW2.Case2Pre.N_F B C.D C.pre] at hnormF
        exact hnormF
      exact hyM hyM'
    have hC3 : 3 ≤ Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) := by
      have hlt : 1 < Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr hCne
      have hoddC : Odd (Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G))) :=
        Odd.of_dvd_nat hodd
          (Subgroup.card_dvd_of_le (inf_le_left : N ⊓ Subgroup.centralizer ({y} : Set G) ≤ N))
      obtain ⟨k, hk⟩ := hoddC
      omega
    have hmul : (Work.GW2.invSet N y).ncard * 3 ≤ 21 * 3 := by
      calc (Work.GW2.invSet N y).ncard * 3
          ≤ (Work.GW2.invSet N y).ncard *
              Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) :=
            Nat.mul_le_mul_left _ hC3
        _ = Nat.card ↥N := h15
        _ ≤ 63 := hN63
        _ = 21 * 3 := by norm_num
    exact Nat.le_of_mul_le_mul_right hmul (by norm_num)


/-! ## Step 2: the even case -/

section EvenCase

variable (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)

/-- `conjSub y A = A` when `y` normalises `A`. -/
theorem conjSub_eq_self_of_mem_normalizer (A : Subgroup G) (y : G)
    (hy : y ∈ Subgroup.normalizer (A : Set G)) : Work.GW2.conjSub y A = A := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff_loc A y x |>.mp hx
    exact (Subgroup.mem_normalizer_iff.mp hy a).mp ha
  · intro x hx
    rw [mem_conjSub_iff_loc]
    refine ⟨y⁻¹ * x * y, ?_, by group⟩
    have hy' : y⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hy
    simpa using (Subgroup.mem_normalizer_iff.mp hy' x).mp hx

/-- `A := C.D.F ⊔ C.D.K = B.U ⊓ C.D.M` is normalised by `H = B.U ⊔ B.S`
(port of `Work.CORE4.A7_FK_normal_H` with `A7Facts3` cut to `A7UData`). -/
theorem A7_FK_normal_H_loc (I : Work.GW2.C4Inputs) (hHyp : Work.GW2.Hyp9 G B C)
    (h2 : Work.GW2.A7Facts2 B C.D)
    (hpre : Work.GW2.Case2Pre B C.D) (hB0F : C.D.B0 = C.D.F)
    (h5 : Work.GW2.A7Facts5 B C.D) :
    B.H ≤ Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) := by
  have hbc : Work.GW2.BenderCtx G := hHyp.1
  have hUM : B.U ⊓ C.D.M = C.D.F ⊔ C.D.K := by
    rw [Work.GW2.Case2Pre.U_eq B C.D hpre, hB0F, sup_comm]
  have hHsplit : B.H = B.U ⊔ (B.S : Subgroup G) := A7Split I hbc h2
  have hSleM : (B.S : Subgroup G) ≤ C.D.M := le_trans h2.2.2.1 (layerIn_le C.D.M)
  have hAnormU : ((C.D.F ⊔ C.D.K).subgroupOf B.U).Normal := h5.2.2
  have hAleU : (C.D.F ⊔ C.D.K) ≤ B.U := hUM ▸ inf_le_left
  have hUleN : B.U ≤ Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAleU).mp hAnormU
  have hSleN : (B.S : Subgroup G) ≤
      Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs a ha
    have hsH : s ∈ B.H := B.S_le_H hs
    have haUM : a ∈ B.U ⊓ C.D.M := by rw [hUM]; exact ha
    obtain ⟨haU, haM⟩ := Subgroup.mem_inf.mp haUM
    have hsU : s * a * s⁻¹ ∈ B.U :=
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal a s haU hsH
    have hsM : s * a * s⁻¹ ∈ C.D.M :=
      C.D.M.mul_mem (C.D.M.mul_mem (hSleM hs) haM) (C.D.M.inv_mem (hSleM hs))
    rw [← hUM]
    exact Subgroup.mem_inf.mpr ⟨hsU, hsM⟩
  rw [hHsplit]
  exact sup_le hUleN hSleN

/-- In the even case (with `y ∈ C_G(t)`), `F ≤ M ⊓ M^y`. -/
theorem F_le_scene (y : G) (hyH : y ∈ B.H) (hpre : Work.GW2.Case2Pre B C.D)
    (hB0F : C.D.B0 = C.D.F) (hAK : C.D.F ≤ C.D.M) (hKK : C.D.K ≤ C.D.M)
    (hHnorm : B.H ≤ Subgroup.normalizer
      (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G)) :
    C.D.F ≤ C.D.M ⊓ Work.GW2.conjSub y C.D.M := by
  have hAy : Work.GW2.conjSub y (C.D.F ⊔ C.D.K) = C.D.F ⊔ C.D.K :=
    conjSub_eq_self_of_mem_normalizer (C.D.F ⊔ C.D.K) y (hHnorm hyH)
  have hAM : C.D.F ⊔ C.D.K ≤ C.D.M := sup_le hAK hKK
  have hAconj : C.D.F ⊔ C.D.K ≤ Work.GW2.conjSub y C.D.M := by
    intro x hx
    have hxA : y⁻¹ * x * y ∈ C.D.F ⊔ C.D.K := by
      have h := (Subgroup.mem_normalizer_iff.mp (hHnorm (B.H.inv_mem hyH)) x).mp hx
      simpa using h
    rw [mem_conjSub_iff_loc]
    exact ⟨y⁻¹ * x * y, hAM hxA, by group⟩
  intro f hf
  exact Subgroup.mem_inf.mpr ⟨hAM (Subgroup.mem_sup_left hf), hAconj (Subgroup.mem_sup_left hf)⟩

end EvenCase

/-- The even case of `A6` when `y ∈ C_G(t)`. -/
theorem A7CosetEvenH (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.CORE4.A7Mid B C.D →
          ∀ y : G, orderOf y = 2 → y ∉ C.D.M → y ∈ B.H →
            (Work.GW2.invSet (C.D.M ⊓ Work.GW2.conjSub y C.D.M) y).ncard ≤ 21 := by
  intro G _ _ B C hHyp hA7 hf1 hf2 hMid y hy2 hyM hyH
  classical
  set V : Subgroup G := Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) with hVdef
  set N : Subgroup G := C.D.M ⊓ Work.GW2.conjSub y C.D.M with hNdef
  show (Work.GW2.invSet N y).ncard ≤ 21
  -- the structure of `N` (delegated)
  obtain ⟨hVN, hVnorm, hodd, hN108, hact⟩ :=
    Work.CORE4.NotA7.A6EvenStructure I G B C hHyp hA7 hf1 hf2 hMid y hy2 hyM hyH
  have hKcard : Nat.card C.D.K = 3 := hf1.1
  have hFcard : Nat.card C.D.F = 3 := hf1.2.1
  have hB0F : C.D.B0 = C.D.F := hMid.1.2.1
  have hFacts5 : Work.GW2.A7Facts5 B C.D := hMid.2.2
  have hseven : Work.GW2.Case2SevenFacts B C.D := hHyp.2.2.2.1
  have hbc : Work.GW2.BenderCtx G := hHyp.1
  have hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M)) := hf2.1
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  -- `y` normalises `N`
  have hmemN : ∀ n : G, n ∈ N ↔ n ∈ C.D.M ∧ ∃ a ∈ C.D.M, y * a * y⁻¹ = n := by
    intro n
    rw [hNdef]
    constructor
    · intro hn
      obtain ⟨hm, hc⟩ := Subgroup.mem_inf.mp hn
      exact ⟨hm, (mem_conjSub_iff_loc C.D.M y n).mp hc⟩
    · rintro ⟨hm, hc⟩
      exact Subgroup.mem_inf.mpr ⟨hm, (mem_conjSub_iff_loc C.D.M y n).mpr hc⟩
  have hstep : ∀ n : G, n ∈ N → y * n * y⁻¹ ∈ N := by
    intro n hn
    obtain ⟨hnM, a, haM, ha⟩ := (hmemN n).mp hn
    rw [hmemN]
    refine ⟨?_, n, hnM, by rfl⟩
    have heq : y * (y * a * y⁻¹) * y⁻¹ = a := by
      have h1' : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hyy, inv_one]
      calc y * (y * a * y⁻¹) * y⁻¹ = (y * y) * a * (y⁻¹ * y⁻¹) := by group
        _ = 1 * a * 1 := by rw [hyy, h1']
        _ = a := by simp
    rw [← ha, heq]
    exact haM
  have hyNnorm : y ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hstep n
    · intro hn
      have h2' := hstep (y * n * y⁻¹) hn
      have heq : y * (y * n * y⁻¹) * y⁻¹ = n := by
        have h1' : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hyy, inv_one]
        calc y * (y * n * y⁻¹) * y⁻¹ = (y * y) * n * (y⁻¹ * y⁻¹) := by group
          _ = 1 * n * 1 := by rw [hyy, h1']
          _ = n := by simp
      rwa [heq] at h2'
  -- `y` normalises `V` (`V ⊴ H`)
  have hVH : B.H ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef, hseven.1]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Work.CORE4.pCoreIn_le_self 2 B.H)).mp (Work.CORE4.subgroupOf_pCoreIn_normal 2 B.H)
  have hyVnorm : y ∈ Subgroup.normalizer (V : Set G) := hVH hyH
  have hyN' : y ∉ N := by
    intro h
    exact hyM ((hmemN y).mp h).1
  -- the counting (delegated)
  have hcount := Work.CORE4.InvSetCountNormalFourB N V y hVN hVnorm hV4 hodd hyNnorm hyVnorm hyy hyN' hact
  -- `6 ∣ |C_N(y)|` (delegated)
  have hC6 : 6 ≤ Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) :=
    Work.CORE4.NotA7.A6EvenCentralizer I G B C y hHyp hA7 hf1 hf2 hMid hy2 hyH hyM
  -- `|I_N(y)| ≤ 108/6 = 18`
  have hI6 : (Work.GW2.invSet N y).ncard * 6 ≤ 108 := by
    calc (Work.GW2.invSet N y).ncard * 6
        ≤ (Work.GW2.invSet N y).ncard *
            Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) := Nat.mul_le_mul_left _ hC6
      _ = Nat.card ↥N := hcount
      _ ≤ 108 := hN108
  have hI18 : (Work.GW2.invSet N y).ncard ≤ 18 :=
    Nat.le_of_mul_le_mul_right (by rw [show (18 : ℕ) * 6 = 108 from rfl]; exact hI6) (by norm_num)
  exact le_trans hI18 (by norm_num)

/-- The even case of `A6` (any involution outside `M` with `|M ⊓ M^y|` even). -/
theorem A7CosetEvenWeak (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.CORE4.A7Mid B C.D →
          ∀ y : G, orderOf y = 2 → y ∉ C.D.M →
            ¬ Odd (Nat.card ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M)) →
              (Work.GW2.invSet (C.D.M ⊓ Work.GW2.conjSub y C.D.M) y).ncard ≤ 21 := by
  intro G _ _ B C hHyp hA7 hf1 hf2 hMid y hy2 hyM hodd
  obtain ⟨y', hy'2, hy'M, hy'H, hy'eq⟩ :=
    Work.CORE4.A7Normalize I G B C hHyp hA7 hf1 hf2 y hy2 hyM hodd
  suffices hgoal : (Work.GW2.invSet (C.D.M ⊓ Work.GW2.conjSub y' C.D.M) y').ncard ≤ 21 by
    rwa [← hy'eq]
  exact A7CosetEvenH I G B C hHyp hA7 hf1 hf2 hMid y' hy'2 hy'M hy'H

theorem A6Weak (I : Work.GW2.C4Inputs) : Work.CORE4.C15.A7CosetWeakProp I := by
  intro G _ _ B C hHyp hA7 hf1 hf2 hMid y hy2 hyM
  have hbridge := ncard_coset_eq_invSet_loc C.D.M y hy2 hyM
  rw [hbridge]
  by_cases hodd : Odd (Nat.card ↥(C.D.M ⊓ Work.GW2.conjSub y C.D.M))
  · exact A7CosetOddWeak I G B C hHyp hA7 hf1 hf2 hMid y hy2 hyM hodd
  · exact A7CosetEvenWeak I G B C hHyp hA7 hf1 hf2 hMid y hy2 hyM hodd

end Work.CORE4.NotA7
