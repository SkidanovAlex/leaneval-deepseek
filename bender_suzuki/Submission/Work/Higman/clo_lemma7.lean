import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.higman_lemma7_phi2
import Submission.Work.Higman.MSA.higman_lemma7_msa

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman

open scoped commutatorElement

/-! ## Elementary numerical facts -/

/-- If `0 < q` and `q ^ e = q ^ (e - 1)` with `1 ≤ e` then `q = 1`. -/
private lemma pow_eq_one_of_pow_pred_eq {q e : ℕ} (hq : 0 < q) (he : 1 ≤ e)
    (h : q ^ e = q ^ (e - 1)) : q = 1 := by
  have h2 : q ^ (e - 1) * q = q ^ (e - 1) * 1 := by
    rw [mul_one, ← pow_succ, show e - 1 + 1 = e from by omega]
    exact h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq (e - 1)) h2

/-- A subgroup of cardinality `1` is trivial. -/
private lemma eq_bot_of_card_eq_one {P : Type} [Group P] {A : Subgroup P}
    (h : Nat.card ↥A = 1) : A = ⊥ := by
  haveI : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp h).1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥A) 1)

/-- The subgroup `W = A ⊓ Ω₁(P)` of involutions of a `ξ`-invariant abelian normal subgroup `A`
of a Suzuki 2-group carries the restricted action of `ξ`; it has exponent two and `ξ` acts
transitively on `W ∖ {1}`. -/
private theorem xiW_aux {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A W : Subgroup P} (hA : IsXiAbelNormal h A) (hW : W = A ⊓ omega1 P) :
    ∃ ξW : MulAut ↥W,
      (∀ x : ↥W, ((ξW x) : P) = h.xi (x : P)) ∧
      (∀ x : ↥W, x * x = 1) ∧
      (∀ a b : ↥W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b) := by
  have hmemA : ∀ x : ↥W, (x : P) ∈ A := fun x =>
    (Subgroup.mem_inf.mp (le_of_eq hW x.2)).1
  have hmemOm : ∀ x : ↥W, (x : P) ∈ omega1 P := fun x =>
    (Subgroup.mem_inf.mp (le_of_eq hW x.2)).2
  have hinvA : ∀ x : ↥W, (h.xi : MulAut P).symm (x : P) ∈ A := fun x =>
    symm_mem_of_map_eq h.xi hA.map_eq (hmemA x)
  have hinvOm : ∀ x : ↥W, (h.xi : MulAut P).symm (x : P) ∈ omega1 P := fun x =>
    symm_mem_of_map_eq h.xi (map_xi_omega1 h) (hmemOm x)
  have hmemXi : ∀ x : ↥W, h.xi (x : P) ∈ W := by
    intro x
    refine le_of_eq hW.symm (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have h' := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) (hmemA x)
      rwa [hA.map_eq] at h'
    · have h' := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) (hmemOm x)
      rwa [map_xi_omega1 h] at h'
  let ξW : MulAut ↥W :=
    { toFun := fun x => ⟨h.xi x, hmemXi x⟩
      invFun := fun x => ⟨(h.xi : MulAut P).symm x, le_of_eq hW.symm
        (Subgroup.mem_inf.mpr ⟨hinvA x, hinvOm x⟩)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hcoe : ∀ (m : ℕ) (x : ↥W), (((ξW ^ m) x : ↥W) : P) = (h.xi ^ m) (x : P) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have hstep : (ξW ^ (n + 1)) x = (ξW ^ n) (ξW x) := by
          rw [pow_succ, MulAut.mul_apply]
        rw [hstep, ih (ξW x)]
        show (h.xi ^ n) (h.xi (x : P)) = (h.xi ^ (n + 1)) (x : P)
        rw [pow_succ, MulAut.mul_apply]
  refine ⟨ξW, fun x => rfl, ?_, ?_⟩
  · intro x
    refine Subtype.ext ?_
    simpa [pow_two] using h.mem_omega1.mp (hmemOm x)
  · intro a b ha hb
    have ha1 : (a : P) ≠ 1 := fun hh => ha (Subtype.ext hh)
    have hb1 : (b : P) ≠ 1 := fun hh => hb (Subtype.ext hh)
    have ha2 : orderOf (a : P) = 2 := by
      have hd : orderOf (a : P) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp (hmemOm a))
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) ha1
      · exact hh
    have hb2 : orderOf (b : P) = 2 := by
      have hd : orderOf (b : P) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp (hmemOm b))
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hb1
      · exact hh
    obtain ⟨k, hk⟩ := h.trans (a : P) (b : P) ha2 hb2
    exact ⟨k, Subtype.ext (by rw [hcoe k a]; exact hk)⟩

/-- **Higman 1963, Suzuki 2-groups, p. 86, auxiliary result 7.** Let `A` be a normal abelian
`ξ`-subgroup of a Suzuki 2-group `P` and `C > A` a normal `ξ`-subgroup covering `A` (`C/A` a
minimal normal `ξ`-section). If `Φ(C) = C²[C,C] = A` and `C' = ⁅C,C⁆ ≤ A²`, then `C` is abelian.

Strategy: `Submission/Work/Higman/MSA_NOTES.md` §5.  Two auxiliary facts are already stated in
`Submission/Work/Higman/higman_lemma7_layer.lean` and
`Submission/Work/Higman/higman_lemma7_comm_le.lean` (import and use them if their owners have
finished them, otherwise reproduce them yourself).  The triviality input for alternating forms is
`Work.Higman.MSA.eq_one_of_alt_of_target_iso` in `Submission/Work/Higman/MSA/basic.lean`; the
homocyclic structure input is `Submission.Work.Higman.homogeneous_structure`. -/
theorem clo_lemma7 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A)
    (hCd : ⁅C, C⁆ ≤ Work.Higman.powSub A 2) :
    ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
  have hAinv := hA.map_eq
  have hAb := hA.abelian
  -- `⁅C,C⁆ ≤ A` because `A = C²[C,C]`
  have hC'le : ⁅C, C⁆ ≤ A := hPhi ▸ le_sup_right
  by_cases hAbot : A = ⊥
  · -- if `A = ⊥` there is nothing to prove
    intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
      rw [← hAbot]
      exact hC'le (Subgroup.commutator_mem_commutator hx hy)
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using hmem)
  · -- from now on `A ≠ ⊥`
    obtain ⟨e, h1, hchain, hker, hinvpow⟩ := homogeneous_structure h hAb hAinv
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | hpos
      · exfalso
        have hcardA : Nat.card ↥A = (Nat.card ↥(A ⊓ omega1 P)) ^ e := by
          have hh := hchain 0 (Nat.zero_le e)
          rw [pow_zero, powSub_one_eq, Nat.sub_zero] at hh
          exact hh
        rw [h0, pow_zero] at hcardA
        exact hAbot (eq_bot_of_card_eq_one hcardA)
      · exact hpos
    have hcard0 : Nat.card ↥A = (Nat.card ↥(A ⊓ omega1 P)) ^ e := by
      have hh := hchain 0 (Nat.zero_le e)
      rw [pow_zero, powSub_one_eq, Nat.sub_zero] at hh
      exact hh
    -- the description of `A²` inside `A`
    have hkey : ∀ y ∈ A, y ∈ powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1 :=
      fun y hy => higman_lemma7_layer_self h hAb he h1 hcard0 1 he y hy
    -- `⁅C,C⁆` is `ξ`-invariant, hence a power subgroup of `A`
    have hC'inv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨s, hs_eq⟩ := hinvpow ⁅C, C⁆ hC'le hC'inv
    by_cases hC'bot : ⁅C, C⁆ = ⊥
    · -- `C` is abelian
      intro x hx y hy
      have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
        rw [← hC'bot]
        exact Subgroup.commutator_mem_commutator hx hy
      exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using hmem)
    · -- the interesting case: `⁅C,C⁆ = A ^ (2 ^ s)` with `1 ≤ s ≤ e - 1`
      have hsle : s ≤ e - 1 := by
        by_contra hcon
        have hes : e ≤ s := by omega
        have hbot : powSub A (2 ^ s) = ⊥ := powSub_eq_bot_of_exp hAb hes h1
        exact hC'bot (by rw [hs_eq, hbot])
      have hs1 : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h0 | hpos
        · exfalso
          subst h0
          have hCA' : ⁅C, C⁆ = A := by rw [hs_eq, pow_zero, powSub_one_eq]
          have hAle : A ≤ powSub A 2 := hCA' ▸ hCd
          have hAeq : powSub A 2 = A := le_antisymm (powSub_le (by norm_num)) hAle
          have hcardA2 : Nat.card ↥(powSub A 2) = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) := by
            have hh := hchain 1 (by omega)
            rw [pow_one] at hh
            exact hh
          have hcardA2' : Nat.card ↥A = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) :=
            (congrArg (fun X : Subgroup P => Nat.card ↥X) hAeq.symm).trans hcardA2
          have hq : Nat.card ↥(A ⊓ omega1 P) = 1 :=
            pow_eq_one_of_pow_pred_eq (Nat.card_pos) he (hcard0.symm.trans hcardA2')
          exact hAbot (eq_bot_of_card_eq_one (by rw [hcard0, hq, one_pow]))
        · exact hpos
      -- the commutator calculus of `Higman 7` (proved in `MSA/higman_lemma7_msa.lean`)
      have hcomm : ⁅A, C⁆ ≤ powSub ⁅C, C⁆ 2 :=
        (higman_lemma7_comm_le_self h hA hCn hAC hPhi hCd hs1 hsle h1 hs_eq).1
      have hcomm' : ⁅⁅C, C⁆, C⁆ ≤ powSub ⁅C, C⁆ 2 :=
        (higman_lemma7_comm_le_self h hA hCn hAC hPhi hCd hs1 hsle h1 hs_eq).2
      -- ## The alternating pairing
      let W : Subgroup P := powSub A (2 ^ (e - 1))
      have hW : W = A ⊓ omega1 P := hker
      have hWleA : W ≤ A := fun x hx => (Subgroup.mem_inf.mp (le_of_eq hW hx)).1
      have hWmemOm : ∀ x : ↥W, (x : P) ∈ omega1 P := fun x =>
        (Subgroup.mem_inf.mp (le_of_eq hW x.2)).2
      letI hWcomm : CommGroup ↥W :=
        { (inferInstance : Group ↥W) with
          mul_comm := fun x y =>
            Subtype.ext (hAb (x : P) (hWleA x.2) (y : P) (hWleA y.2)) }
      have hWsq : ∀ x : ↥W, x * x = 1 := by
        intro x
        refine Subtype.ext ?_
        simpa [pow_two] using h.mem_omega1.mp (hWmemOm x)
      obtain ⟨ξW, hξW, -, hWtrans⟩ := xiW_aux h hA hW
      -- `φ : C → W`, `x ↦ x ^ 2 ^ e`, with kernel `A`
      obtain ⟨hphi_hom, hphi_img, hphi_surj, hphi_ker, hphi_xi⟩ :=
        higman_lemma7_phi2 h hA hCn hCinv hAC hCA hcover hPhi hCd hAbot he h1 hkey hker
      -- choose representatives in `C` of the elements of `W`
      have hsurj : ∀ w : ↥W, ∃ x : P, x ∈ C ∧ x ^ 2 ^ e = (w : P) := fun w =>
        hphi_surj (w : P) (le_of_eq hW w.2)
      let rep : ↥W → P := fun w => Classical.choose (hsurj w)
      have rep_mem : ∀ w : ↥W, rep w ∈ C := fun w => (Classical.choose_spec (hsurj w)).1
      have rep_spec : ∀ w : ↥W, rep w ^ 2 ^ e = (w : P) :=
        fun w => (Classical.choose_spec (hsurj w)).2
      let k : ℕ := e - 1 - s
      have hk : 2 ^ s * 2 ^ k = 2 ^ (e - 1) := by
        rw [← pow_add]; congr 1; omega
      -- the values of the pairing lie in `W`
      have hval : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ^ 2 ^ k ∈ W := by
        intro x hx y hy
        have hmem : ⁅x, y⁆ ∈ powSub A (2 ^ s) := by
          rw [← hs_eq]
          exact Subgroup.commutator_mem_commutator hx hy
        obtain ⟨a, ha, hae⟩ := (mem_powSub_iff hAb).mp hmem
        rw [← hae, ← pow_mul, hk]
        exact pow_mem_powSub ha
      let c : ↥W → ↥W → ↥W := fun w w' =>
        ⟨⁅rep w, rep w'⁆ ^ 2 ^ k, hval (rep w) (rep_mem w) (rep w') (rep_mem w')⟩
      -- ## commutator calculus for the pairing
      have hsub2 : powSub ⁅C, C⁆ 2 = powSub A (2 ^ (s + 1)) := by
        rw [hs_eq, powSub_powSub hAb (2 ^ s) 2, ← pow_succ]
      have hC'ab : ∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆, u * v = v * u :=
        fun u hu v hv => hAb u (hC'le hu) v (hC'le hv)
      have hpowmem : ∀ u ∈ ⁅C, C⁆, u ^ 2 ^ k ∈ ⁅C, C⁆ := fun u hu =>
        powSub_le (pow_pos (by norm_num) k) (pow_mem_powSub hu)
      -- `(C')²` is killed by the `2 ^ k`-th power map
      have hkill : ∀ t ∈ powSub ⁅C, C⁆ 2, t ^ 2 ^ k = 1 := by
        intro t ht
        rw [hsub2] at ht
        obtain ⟨a, ha, hae⟩ := (mem_powSub_iff hAb).mp ht
        rw [← hae, ← pow_mul]
        rw [show 2 ^ (s + 1) * 2 ^ k = 2 ^ e from by rw [← pow_add]; congr 1; omega]
        exact h1 a ha
      -- powers of products of three commuting elements
      have hmul3 : ∀ (u v w : P) (n : ℕ), Commute u v → Commute u w → Commute v w →
          (u * v * w) ^ n = u ^ n * v ^ n * w ^ n := by
        intro u v w n huv huw hvw
        rw [Commute.mul_pow (huw.mul_left hvw) n, Commute.mul_pow huv n]
      -- ### invariance of the pairing under multiplying an argument by an element of `A`
      have hid1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x * y⁻¹ ∈ A →
          ⁅x, z⁆ ^ 2 ^ k = ⁅y, z⁆ ^ 2 ^ k := by
        intro x hx y hy z hz hxy
        have haC : x * y⁻¹ ∈ C := C.mul_mem hx (C.inv_mem hy)
        have hyzC' : ⁅y, z⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hy hz
        have hyzC : ⁅y, z⁆ ∈ C := hAC (hC'le hyzC')
        have hp1C' : ⁅x * y⁻¹, ⁅y, z⁆⁆ ∈ ⁅C, C⁆ :=
          Subgroup.commutator_mem_commutator haC hyzC
        have hp2C' : ⁅x * y⁻¹, z⁆ ∈ ⁅C, C⁆ :=
          Subgroup.commutator_mem_commutator haC hz
        have hp1kill : ⁅x * y⁻¹, ⁅y, z⁆⁆ ^ 2 ^ k = 1 :=
          hkill _ (hcomm (Subgroup.commutator_mem_commutator hxy hyzC))
        have hp2kill : ⁅x * y⁻¹, z⁆ ^ 2 ^ k = 1 :=
          hkill _ (hcomm (Subgroup.commutator_mem_commutator hxy hz))
        have hdec : ⁅x, z⁆ = ⁅x * y⁻¹, ⁅y, z⁆⁆ * ⁅y, z⁆ * ⁅x * y⁻¹, z⁆ := by
          rw [show x = (x * y⁻¹) * y from by group, commutatorElement_def]
          group
        rw [hdec, hmul3 _ _ _ _
            (hC'ab _ hp1C' _ hyzC') (hC'ab _ hp1C' _ hp2C') (hC'ab _ hyzC' _ hp2C')]
        simp [hp1kill, hp2kill]
      have hid2 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x * y⁻¹ ∈ A →
          ⁅z, x⁆ ^ 2 ^ k = ⁅z, y⁆ ^ 2 ^ k := by
        intro x hx y hy z hz hxy
        have haC : x * y⁻¹ ∈ C := C.mul_mem hx (C.inv_mem hy)
        have hzyC' : ⁅z, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hz hy
        have hzyC : ⁅z, y⁆ ∈ C := hAC (hC'le hzyC')
        have hq1C' : ⁅z, x * y⁻¹⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hz haC
        have hq2C' : ⁅x * y⁻¹, ⁅z, y⁆⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator haC hzyC
        have hq1kill : ⁅z, x * y⁻¹⁆ ^ 2 ^ k = 1 :=
          hkill _ (hcomm ((Subgroup.commutator_comm C A) ▸
            Subgroup.commutator_mem_commutator hz hxy))
        have hq2kill : ⁅x * y⁻¹, ⁅z, y⁆⁆ ^ 2 ^ k = 1 :=
          hkill _ (hcomm (Subgroup.commutator_mem_commutator hxy hzyC))
        have hdec : ⁅z, x⁆ = ⁅z, x * y⁻¹⁆ * ⁅x * y⁻¹, ⁅z, y⁆⁆ * ⁅z, y⁆ := by
          rw [show x = (x * y⁻¹) * y from by group, commutatorElement_def]
          group
        rw [hdec, hmul3 _ _ _ _
            (hC'ab _ hq1C' _ hq2C') (hC'ab _ hq1C' _ hzyC') (hC'ab _ hq2C' _ hzyC')]
        simp [hq1kill, hq2kill]
      -- ### biadditivity of the pairing
      have hid3 : ∀ x ∈ C, ∀ x' ∈ C, ∀ z ∈ C,
          ⁅x * x', z⁆ ^ 2 ^ k = ⁅x, z⁆ ^ 2 ^ k * ⁅x', z⁆ ^ 2 ^ k := by
        intro x hx x' hx' z hz
        have hxzC' : ⁅x, z⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hz
        have hx'zC' : ⁅x', z⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx' hz
        have hx'zC : ⁅x', z⁆ ∈ C := hAC (hC'le hx'zC')
        have hpC'' : ⁅x, ⁅x', z⁆⁆ ∈ ⁅C, ⁅C, C⁆⁆ :=
          Subgroup.commutator_mem_commutator (H₂ := ⁅C, C⁆) hx hx'zC'
        have hpC' : ⁅x, ⁅x', z⁆⁆ ∈ ⁅C, C⁆ :=
          powSub_le (by norm_num) (hcomm' ((Subgroup.commutator_comm C ⁅C, C⁆) ▸ hpC''))
        have hpkill : ⁅x, ⁅x', z⁆⁆ ^ 2 ^ k = 1 :=
          hkill _ (hcomm' ((Subgroup.commutator_comm C ⁅C, C⁆) ▸ hpC''))
        have hdec : ⁅x * x', z⁆ = ⁅x, ⁅x', z⁆⁆ * ⁅x', z⁆ * ⁅x, z⁆ := by
          rw [commutatorElement_def]
          group
        rw [hdec, hmul3 _ _ _ _
            (hC'ab _ hpC' _ hx'zC') (hC'ab _ hpC' _ hxzC') (hC'ab _ hx'zC' _ hxzC'),
          hpkill, one_mul]
        exact hC'ab _ (hpowmem _ hx'zC') _ (hpowmem _ hxzC')
      have hid4 : ∀ z ∈ C, ∀ x ∈ C, ∀ x' ∈ C,
          ⁅z, x * x'⁆ ^ 2 ^ k = ⁅z, x⁆ ^ 2 ^ k * ⁅z, x'⁆ ^ 2 ^ k := by
        intro z hz x hx x' hx'
        have hzxC' : ⁅z, x⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hz hx
        have hzx'C' : ⁅z, x'⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hz hx'
        have hzx'C : ⁅z, x'⁆ ∈ C := hAC (hC'le hzx'C')
        have hpC'' : ⁅x, ⁅z, x'⁆⁆ ∈ ⁅C, ⁅C, C⁆⁆ :=
          Subgroup.commutator_mem_commutator (H₂ := ⁅C, C⁆) hx hzx'C'
        have hpC' : ⁅x, ⁅z, x'⁆⁆ ∈ ⁅C, C⁆ :=
          powSub_le (by norm_num) (hcomm' ((Subgroup.commutator_comm C ⁅C, C⁆) ▸ hpC''))
        have hpkill : ⁅x, ⁅z, x'⁆⁆ ^ 2 ^ k = 1 :=
          hkill _ (hcomm' ((Subgroup.commutator_comm C ⁅C, C⁆) ▸ hpC''))
        have hdec : ⁅z, x * x'⁆ = ⁅z, x⁆ * ⁅x, ⁅z, x'⁆⁆ * ⁅z, x'⁆ := by
          rw [commutatorElement_def]
          group
        rw [hdec, hmul3 _ _ _ _
            (hC'ab _ hzxC' _ hpC') (hC'ab _ hzxC' _ hzx'C') (hC'ab _ hpC' _ hzx'C'),
          hpkill, mul_one]
      -- equal `φ`-images differ by an element of `A`
      have hdiff : ∀ x y : P, x ∈ C → y ∈ C → x ^ 2 ^ e = y ^ 2 ^ e → x * y⁻¹ ∈ A := by
        intro x y hx hy hxy
        refine (hphi_ker _ (C.mul_mem hx (C.inv_mem hy))).mp ?_
        rw [hphi_hom x hx y⁻¹ (C.inv_mem hy), inv_pow, hxy, mul_inv_cancel]
      -- ## `c` is an alternating biadditive `ξ`-equivariant pairing
      have hc_alt : ∀ w : ↥W, c w w = 1 := by
        intro w
        refine Subtype.ext ?_
        show ⁅rep w, rep w⁆ ^ 2 ^ k = (1 : P)
        rw [commutatorElement_self, one_pow]
      have hc_mul : ∀ w w' w'' : ↥W, c (w * w') w'' = c w w'' * c w' w'' := by
        intro w w' w''
        have hsame : rep (w * w') * (rep w * rep w')⁻¹ ∈ A := by
          refine hdiff (rep (w * w')) (rep w * rep w') (rep_mem _)
            (C.mul_mem (rep_mem w) (rep_mem w')) ?_
          rw [rep_spec (w * w'),
            hphi_hom (rep w) (rep_mem w) (rep w') (rep_mem w'), rep_spec w, rep_spec w']
          simp
        refine Subtype.ext ?_
        show ⁅rep (w * w'), rep w''⁆ ^ 2 ^ k
          = ⁅rep w, rep w''⁆ ^ 2 ^ k * ⁅rep w', rep w''⁆ ^ 2 ^ k
        rw [hid1 (rep (w * w')) (rep_mem _) (rep w * rep w')
            (C.mul_mem (rep_mem w) (rep_mem w')) (rep w'') (rep_mem _) hsame,
          hid3 (rep w) (rep_mem w) (rep w') (rep_mem w') (rep w'') (rep_mem w'')]
      have hc_mul' : ∀ w w' w'' : ↥W, c w (w' * w'') = c w w' * c w w'' := by
        intro w w' w''
        have hsame : rep (w' * w'') * (rep w' * rep w'')⁻¹ ∈ A := by
          refine hdiff (rep (w' * w'')) (rep w' * rep w'') (rep_mem _)
            (C.mul_mem (rep_mem w') (rep_mem w'')) ?_
          rw [rep_spec (w' * w''),
            hphi_hom (rep w') (rep_mem w') (rep w'') (rep_mem w''), rep_spec w', rep_spec w'']
          simp
        refine Subtype.ext ?_
        show ⁅rep w, rep (w' * w'')⁆ ^ 2 ^ k
          = ⁅rep w, rep w'⁆ ^ 2 ^ k * ⁅rep w, rep w''⁆ ^ 2 ^ k
        rw [hid2 (rep (w' * w'')) (rep_mem _) (rep w' * rep w'')
            (C.mul_mem (rep_mem w') (rep_mem w'')) (rep w) (rep_mem w) hsame,
          hid4 (rep w) (rep_mem w) (rep w') (rep_mem w') (rep w'') (rep_mem w'')]
      have hc_eq : ∀ w w' : ↥W, ξW (c w w') = c (ξW w) (ξW w') := by
        intro w w'
        have hxiC : ∀ z ∈ C, h.xi z ∈ C := by
          intro z hz
          have h' := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) hz
          rwa [hCinv] at h'
        have hs1' : rep (ξW w) * (h.xi (rep w))⁻¹ ∈ A := by
          refine hdiff (rep (ξW w)) (h.xi (rep w)) (rep_mem _) (hxiC _ (rep_mem w)) ?_
          rw [rep_spec (ξW w), ← map_pow, rep_spec w, hξW w]
        have hs2' : rep (ξW w') * (h.xi (rep w'))⁻¹ ∈ A := by
          refine hdiff (rep (ξW w')) (h.xi (rep w')) (rep_mem _) (hxiC _ (rep_mem w')) ?_
          rw [rep_spec (ξW w'), ← map_pow, rep_spec w', hξW w']
        have hstep : ⁅h.xi (rep w), h.xi (rep w')⁆ ^ 2 ^ k
            = ⁅rep (ξW w), rep (ξW w')⁆ ^ 2 ^ k := by
          rw [← hid1 (rep (ξW w)) (rep_mem _) (h.xi (rep w))
              (hxiC _ (rep_mem w)) (h.xi (rep w')) (hxiC _ (rep_mem w')) hs1',
            ← hid2 (rep (ξW w')) (rep_mem _) (h.xi (rep w'))
              (hxiC _ (rep_mem w')) (rep (ξW w)) (rep_mem _) hs2']
        refine Subtype.ext ?_
        show ((ξW (c w w') : ↥W) : P) = (c (ξW w) (ξW w') : P)
        rw [hξW (c w w')]
        show h.xi (⁅rep w, rep w'⁆ ^ 2 ^ k) = _
        rw [map_pow, map_commutatorElement]
        exact hstep
      -- ## the pairing is trivial
      have htriv_c : ∀ w w' : ↥W, c w w' = 1 :=
        equivariant_bihom_trivial hWsq ξW hWtrans c hc_mul hc_mul' hc_alt hc_eq
      -- ## consequently `⁅x,y⁆ ^ 2 ^ k = 1` for all `x, y ∈ C`
      have htriv : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ^ 2 ^ k = 1 := by
        intro x hx y hy
        have hxW : x ^ 2 ^ e ∈ W := le_of_eq hW.symm (hphi_img x hx)
        have hyW : y ^ 2 ^ e ∈ W := le_of_eq hW.symm (hphi_img y hy)
        have hdx : rep ⟨x ^ 2 ^ e, hxW⟩ * x⁻¹ ∈ A := by
          refine hdiff (rep ⟨x ^ 2 ^ e, hxW⟩) x (rep_mem _) hx ?_
          rw [rep_spec]
        have hdy : rep ⟨y ^ 2 ^ e, hyW⟩ * y⁻¹ ∈ A := by
          refine hdiff (rep ⟨y ^ 2 ^ e, hyW⟩) y (rep_mem _) hy ?_
          rw [rep_spec]
        have hzero : ⁅rep ⟨x ^ 2 ^ e, hxW⟩, rep ⟨y ^ 2 ^ e, hyW⟩⁆ ^ 2 ^ k = 1 := by
          have h' : (c ⟨x ^ 2 ^ e, hxW⟩ ⟨y ^ 2 ^ e, hyW⟩ : ↥W) = 1 :=
            htriv_c ⟨x ^ 2 ^ e, hxW⟩ ⟨y ^ 2 ^ e, hyW⟩
          exact congrArg (fun t : ↥W => (t : P)) h'
        rw [← hid2 (rep ⟨y ^ 2 ^ e, hyW⟩) (rep_mem _) y hy x hx hdy,
          ← hid1 (rep ⟨x ^ 2 ^ e, hxW⟩) (rep_mem _) x hx
            (rep ⟨y ^ 2 ^ e, hyW⟩) (rep_mem _) hdx]
        exact hzero
      -- ## `⁅C,C⁆ ≤ (⁅C,C⁆)²`, which is impossible by the homocyclic structure
      have hsq : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ powSub ⁅C, C⁆ 2 := by
        intro x hx y hy
        have hmem : ⁅x, y⁆ ∈ powSub A (2 ^ s) := by
          rw [← hs_eq]
          exact Subgroup.commutator_mem_commutator hx hy
        obtain ⟨a, ha, hae⟩ := (mem_powSub_iff hAb).mp hmem
        have hae1 : a ^ 2 ^ (e - 1) = 1 := by
          have h' := htriv x hx y hy
          rw [← hae, ← pow_mul,
            show 2 ^ s * 2 ^ k = 2 ^ (e - 1) from by rw [← pow_add]; congr 1; omega] at h'
          exact h'
        obtain ⟨b, hb, hbe⟩ := (mem_powSub_iff hAb).mp ((hkey a ha).mpr hae1)
        have hexp : 2 * 2 ^ s = 2 ^ (s + 1) := by rw [mul_comm 2 (2 ^ s), pow_succ]
        have hbpow : ⁅x, y⁆ = b ^ 2 ^ (s + 1) := by
          rw [← hae, ← hbe, ← pow_mul, hexp]
        rw [hbpow, hsub2]
        exact pow_mem_powSub hb
      have hC'le2 : ⁅C, C⁆ ≤ powSub ⁅C, C⁆ 2 := by
        rw [Subgroup.commutator_def, Subgroup.closure_le]
        rintro v ⟨x, hx, y, hy, rfl⟩
        exact hsq x hx y hy
      have hC'eq2 : ⁅C, C⁆ = powSub ⁅C, C⁆ 2 :=
        le_antisymm hC'le2 (powSub_le (by norm_num))
      have hcard1 : Nat.card ↥(⁅C, C⁆) = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s) := by
        rw [hs_eq]; exact hchain s (by omega)
      have hcard2 : Nat.card ↥(powSub ⁅C, C⁆ 2)
          = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s - 1) := by
        rw [hsub2]
        have hh := hchain (s + 1) (by omega)
        rw [show e - (s + 1) = e - s - 1 from by omega] at hh
        exact hh
      have hq1 : Nat.card ↥(A ⊓ omega1 P) = 1 :=
        pow_eq_one_of_pow_pred_eq (Nat.card_pos) (by omega)
          (hcard1.symm.trans ((congrArg (fun X : Subgroup P => Nat.card ↥X) hC'eq2).trans hcard2))
      have hAcard1 : Nat.card ↥A = 1 := by
        rw [hcard0, hq1, one_pow]
      exfalso
      exact hAbot (eq_bot_of_card_eq_one hAcard1)

end Work.Higman
