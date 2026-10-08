import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.Higman.higman_lemma7_phi2
import Submission.Work.Higman.higman_lemma8
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.endgame
import Submission.Work.Higman.MSA.exp_four
import Submission.Work.Higman.center_eq_omega1
import Submission.Work.GlaubermanZJ.Thm41.commutator_lowerCentralSeries_le
import Submission.Work.Higman.higman_lemma3_base
import Submission.Work.Higman.clo_lemma3
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.powSub_normal
import Submission.Work.Higman.higman9_derivation_kernel

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

variable {P : Type} [Group P] [Finite P]

/-! ## Elementary helper lemmas -/

/-- If `A < C` (`A ≤ C`, `A ≠ C`) then some element of `C` lies outside `A`. -/
theorem exists_mem_notMem_of_ne {A C : Subgroup P} (hAC : A ≤ C) (hne : A ≠ C) :
    ∃ x : P, x ∈ C ∧ x ∉ A := by
  by_contra hcon
  push_neg at hcon
  exact hne (le_antisymm hAC fun x hx => hcon x hx)

/-- An element of a subgroup contained in the centralizer of `A` commutes with `A`. -/
theorem commutator_eq_one_of_mem_centralizer {A C : Subgroup P}
    (hCcent : C ≤ Subgroup.centralizer (A : Set P)) {c : P} (hc : c ∈ C) {a : P} (ha : a ∈ A) :
    ⁅c, a⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_iff.mp (hCcent hc) a ha).symm

/-! ## The commutator of a normal subgroup inside the centralizer of an abelian normal subgroup
is elementary abelian -/

/-- **Step:** let `A ≤ C` with `A` abelian, `C` centralizing `A`, `powSub C 2 ≤ A` and
`⁅C,C⁆ ≤ A`.  Then `⁅C,C⁆ ≤ Ω₁(P)`: `C` has class two (`⁅C,C⁆ ≤ A ≤ Z(C)`), so for `x, c ∈ C`
the map `y ↦ ⁅y, c⁆` is a homomorphism and `⁅x², c⁆ = ⁅x, c⁆² = 1` because `x² ∈ C² ⊆ A`
commutes with `c`. -/
theorem commutator_le_omega1_of_le_centralizer {A C : Subgroup P}
    (h : IsSuzuki2Grp P) (hAC : A ≤ C) (hCcent : C ≤ Subgroup.centralizer (A : Set P))
    (hC2A : powSub C 2 ≤ A) (hCdA : ⁅C, C⁆ ≤ A) :
    ⁅C, C⁆ ≤ omega1 P := by
  rw [Subgroup.commutator_le]
  intro x hx c hc
  rw [h.mem_omega1]
  have hxcA : ⁅x, c⁆ ∈ A := hCdA (Subgroup.commutator_mem_commutator hx hc)
  have hxxA : x * x ∈ A := by
    have h1 : x ^ 2 ∈ powSub C 2 := pow_mem_powSub (n := 2) hx
    rw [pow_two] at h1
    exact hC2A h1
  have h1 : ⁅x * x, c⁆ = 1 := by
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    exact Subgroup.mem_centralizer_iff.mp (hCcent hc) (x * x) hxxA
  have h2 : ⁅x * x, c⁆ = ⁅x, c⁆ * ⁅x, c⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul x x c]
    have hcx : x * ⁅x, c⁆ = ⁅x, c⁆ * x :=
      (Subgroup.mem_centralizer_iff.mp (hCcent hx) ⁅x, c⁆ hxcA).symm
    rw [show x * ⁅x, c⁆ * x⁻¹ = ⁅x, c⁆ from by
      rw [hcx, mul_assoc, mul_inv_cancel, mul_one]]
  rw [h2] at h1
  simpa [pow_two] using h1

/-! ## A `2`-group with a unique nontrivial abelian normal subgroup has class two -/

/-- **Step:** if a Suzuki 2-group `P` has a unique nontrivial `ξ`-invariant abelian normal
subgroup `A`, then `P` has class at most two, i.e. `(⊤ : Subgroup P).lowerCentralSeries 2 = ⊥`.

Indeed, if `γₖ` denotes the lower central series (with `γ₀ = ⊤`), take the least `e` with
`γ_e = ⊥`; then `e ≥ 3` under the assumption `γ_2 ≠ ⊥`, and `γ_{e-1}`, `γ_{e-2}` are both
nontrivial abelian (by `commutator_lowerCentralSeries_le`) normal `ξ`-invariant subgroups, hence
both equal `A`; but `γ_{e-1} = ⁅γ_{e-2}, ⊤⁆ = ⁅γ_{e-1}, ⊤⁆ = γ_e = ⊥`, a contradiction. -/
theorem lowerCentralSeries_two_eq_bot_of_unique_abelian_normal {A : Subgroup P}
    (h : IsSuzuki2Grp P)
    (huniq : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → B ≠ ⊥ → B = A) :
    (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ := by
  classical
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnil : Group.IsNilpotent P := h.isPGroup.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := P)).mp hnil
  haveI htopchar : (⊤ : Subgroup P).Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    exact Subgroup.map_top_of_surjective _ φ.surjective
  have htop_ne_bot : (⊤ : Subgroup P) ≠ ⊥ := by
    intro hc
    obtain ⟨x, y, hx2, hy2, hxy⟩ := h.manyInvol
    have hx1 : x ≠ 1 := by rintro rfl; exact absurd hx2 (by simp)
    have hmem : x ∈ (⊥ : Subgroup P) := by rw [← hc]; exact Subgroup.mem_top x
    exact hx1 (Subgroup.mem_bot.mp hmem)
  have hex : ∃ k, (⊤ : Subgroup P).lowerCentralSeries k = ⊥ := ⟨n, hn⟩
  let e := Nat.find hex
  have he_spec : (⊤ : Subgroup P).lowerCentralSeries e = ⊥ := Nat.find_spec hex
  have he_min : ∀ m, m < e → (⊤ : Subgroup P).lowerCentralSeries m ≠ ⊥ :=
    fun m hm => Nat.find_min hex hm
  have hγ1 : (⊤ : Subgroup P).lowerCentralSeries 1 ≠ ⊥ := by
    intro hc
    apply hne
    rw [Subgroup.lowerCentralSeries_succ, hc, Subgroup.commutator_bot_left]
  have he3 : 3 ≤ e := by
    by_contra hcon
    interval_cases e
    · exact htop_ne_bot (by simpa using he_spec)
    · exact hγ1 he_spec
    · exact hne he_spec
  have hEm1 : (⊤ : Subgroup P).lowerCentralSeries (e - 1) ≠ ⊥ := he_min _ (by omega)
  have hEm2 : (⊤ : Subgroup P).lowerCentralSeries (e - 2) ≠ ⊥ := he_min _ (by omega)
  have hab1 : ∀ x ∈ (⊤ : Subgroup P).lowerCentralSeries (e - 1),
      ∀ y ∈ (⊤ : Subgroup P).lowerCentralSeries (e - 1), x * y = y * x := by
    intro x hx y hy
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P).lowerCentralSeries (e - 1),
        (⊤ : Subgroup P).lowerCentralSeries (e - 1)⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    have hle := Work.GlaubermanZJ.Thm41.commutator_lowerCentralSeries_le (⊤ : Subgroup P)
      (e - 1) (e - 1)
    have hsub : (⊤ : Subgroup P).lowerCentralSeries ((e - 1) + (e - 1) + 1)
        ≤ (⊤ : Subgroup P).lowerCentralSeries e :=
      Subgroup.lowerCentralSeries_antitone ⊤ (by omega)
    have hmem' : ⁅x, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries e := hsub (hle hmem)
    rw [he_spec] at hmem'
    simpa using hmem'
  have hab2 : ∀ x ∈ (⊤ : Subgroup P).lowerCentralSeries (e - 2),
      ∀ y ∈ (⊤ : Subgroup P).lowerCentralSeries (e - 2), x * y = y * x := by
    intro x hx y hy
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P).lowerCentralSeries (e - 2),
        (⊤ : Subgroup P).lowerCentralSeries (e - 2)⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    have hle := Work.GlaubermanZJ.Thm41.commutator_lowerCentralSeries_le (⊤ : Subgroup P)
      (e - 2) (e - 2)
    have hsub : (⊤ : Subgroup P).lowerCentralSeries ((e - 2) + (e - 2) + 1)
        ≤ (⊤ : Subgroup P).lowerCentralSeries e :=
      Subgroup.lowerCentralSeries_antitone ⊤ (by omega)
    have hmem' : ⁅x, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries e := hsub (hle hmem)
    rw [he_spec] at hmem'
    simpa using hmem'
  have hchar1 : ((⊤ : Subgroup P).lowerCentralSeries (e - 1)).Characteristic :=
    Subgroup.lowerCentralSeries_characteristic ⊤ (e - 1)
  have hchar2 : ((⊤ : Subgroup P).lowerCentralSeries (e - 2)).Characteristic :=
    Subgroup.lowerCentralSeries_characteristic ⊤ (e - 2)
  have hnorm1 : ((⊤ : Subgroup P).lowerCentralSeries (e - 1)).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    exact Subgroup.characteristic_iff_map_eq.mp hchar1 (MulAut.conj g)
  have hnorm2 : ((⊤ : Subgroup P).lowerCentralSeries (e - 2)).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    exact Subgroup.characteristic_iff_map_eq.mp hchar2 (MulAut.conj g)
  have hxi1 : ((⊤ : Subgroup P).lowerCentralSeries (e - 1)).map (h.xi : MulAut P).toMonoidHom
      = (⊤ : Subgroup P).lowerCentralSeries (e - 1) :=
    Subgroup.characteristic_iff_map_eq.mp hchar1 (h.xi : MulAut P)
  have hxi2 : ((⊤ : Subgroup P).lowerCentralSeries (e - 2)).map (h.xi : MulAut P).toMonoidHom
      = (⊤ : Subgroup P).lowerCentralSeries (e - 2) :=
    Subgroup.characteristic_iff_map_eq.mp hchar2 (h.xi : MulAut P)
  have hEq1 : (⊤ : Subgroup P).lowerCentralSeries (e - 1) = A := huniq _ hnorm1 hxi1 hab1 hEm1
  have hEq2 : (⊤ : Subgroup P).lowerCentralSeries (e - 2) = A := huniq _ hnorm2 hxi2 hab2 hEm2
  have hconj : (⊤ : Subgroup P).lowerCentralSeries (e - 1)
      = ⁅(⊤ : Subgroup P).lowerCentralSeries (e - 2), ⊤⁆ := by
    have h1 : e - 1 = (e - 2) + 1 := by omega
    rw [h1, Subgroup.lowerCentralSeries_succ]
  have hstep : ⁅(⊤ : Subgroup P).lowerCentralSeries (e - 1), ⊤⁆
      = (⊤ : Subgroup P).lowerCentralSeries e := by
    rw [← Subgroup.lowerCentralSeries_succ]
    congr 1
    omega
  rw [hEq2, ← hEq1] at hconj
  have : (⊤ : Subgroup P).lowerCentralSeries (e - 1) = ⊥ := by
    rw [hconj, hstep]
    exact he_spec
  exact hEm1 this

/-! ## The exponent datum of a homocyclic `ξ`-invariant abelian normal subgroup -/

/-- **Step.**  With the exponent data of `homogeneous_structure` (`2 ^ e` the exponent,
`|A ^ (2 ^ i)| = q ^ (e - i)`), the subgroup `A²` is exactly the kernel of the
`2 ^ (e - 1)`-st power map on `A`. -/
theorem mem_powSub_two_iff_of_homogeneous {A : Subgroup P}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e : ℕ} (he : 1 ≤ e)
    (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hcard : ∀ i ≤ e, Nat.card ↥(powSub A (2 ^ i))
      = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - i)) :
    ∀ y ∈ A, y ∈ powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1 := by
  intro y hy
  have he1 : 2 * 2 ^ (e - 1) = 2 ^ e := by rw [mul_comm, ← pow_succ]; congr 1; omega
  set q : ℕ := Nat.card ↥(A ⊓ omega1 P) with hq
  have hqpos : 0 < q := Nat.card_pos
  constructor
  · intro hy2
    obtain ⟨z, hz, hzy⟩ := (mem_powSub_iff hab).mp hy2
    rw [← hzy, ← pow_mul, he1]
    exact h1 z hz
  · intro hy1
    let f : ↥A →* ↥A :=
      { toFun := fun z => z ^ 2 ^ (e - 1)
        map_one' := by simp
        map_mul' := fun u v => by
          have hc : Commute u v := Subtype.ext (hab u u.2 v v.2)
          exact hc.mul_pow (2 ^ (e - 1)) }
    have hrange : Nat.card ↥f.range = q := by
      have hmap : Subgroup.map A.subtype f.range = powSub A (2 ^ (e - 1)) := by
        apply le_antisymm
        · rintro w ⟨z, hz, rfl⟩
          obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hz
          exact pow_mem_powSub u.2
        · intro w hw
          rw [mem_powSub_iff hab] at hw
          obtain ⟨u, hu, rfl⟩ := hw
          exact ⟨⟨u, hu⟩ ^ 2 ^ (e - 1), ⟨⟨u, hu⟩, rfl⟩, rfl⟩
      have hcardmap := Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective
        (K := f.range)
      rw [hmap, hcard (e - 1) (by omega), Nat.sub_sub_self he, pow_one] at hcardmap
      exact hcardmap.symm
    have hcardA : Nat.card ↥A = q ^ e := by
      have h0 := hcard 0 (Nat.zero_le e)
      rw [pow_zero, powSub_one_eq, Nat.sub_zero] at h0
      exact h0
    have hcard1 : Nat.card ↥(powSub A 2) = q ^ (e - 1) := by
      have h1' := hcard 1 (by omega)
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num] at h1'
      exact h1'
    have hker : Nat.card ↥f.ker = q ^ (e - 1) := by
      have hcm := card_ker_mul_card_range f
      rw [hrange, hcardA, hq] at hcm
      have heq : q ^ e = q ^ (e - 1) * q := by
        rw [← pow_succ]
        congr 1
        omega
      rw [heq] at hcm
      exact Nat.eq_of_mul_eq_mul_right hqpos hcm
    have hle : powSub A 2 ≤ Subgroup.map A.subtype f.ker := by
      intro w hw
      obtain ⟨u, hu, huw⟩ := (mem_powSub_iff hab).mp hw
      refine Subgroup.mem_map.mpr ⟨⟨u * u, A.mul_mem hu hu⟩, ?_, ?_⟩
      · rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change ((u * u) ^ 2 ^ (e - 1) : P) = (1 : P)
        rw [show u * u = u ^ 2 from (pow_two u).symm, ← pow_mul, he1]
        exact h1 u hu
      · simpa [pow_two] using huw
    have hcard2 : Nat.card ↥(Subgroup.map A.subtype f.ker) = q ^ (e - 1) := by
      rw [Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective (K := f.ker), hker]
    have heqker : powSub A 2 = Subgroup.map A.subtype f.ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
    have hyker : (⟨y, hy⟩ : ↥A) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change (⟨y, hy⟩ : ↥A) ^ 2 ^ (e - 1) = 1
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hy1
    have hy2 : y ∈ Subgroup.map A.subtype f.ker :=
      Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hyker, rfl⟩
    rwa [← heqker] at hy2

/-! ## The restricted `ξ`-action on `A ⊓ Ω₁(P)` -/

/-- `W := A ⊓ Ω₁(P)` carries the restricted `ξ`-action; it is elementary abelian and `ξ` is
transitive on `W ∖ {1}`. -/
theorem exists_xiMulAut_inf_omega1 (h : IsSuzuki2Grp P) {A W : Subgroup P}
    (hA : IsXiAbelNormal h A) (hW : W = A ⊓ omega1 P) :
    ∃ ξW : MulAut ↥W,
      (∀ x : ↥W, ((ξW x : ↥W) : P) = h.xi (x : P)) ∧
      (∀ x : ↥W, x * x = 1) ∧
      (∀ a b : ↥W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b) := by
  have hmem : ∀ x : ↥W, (x : P) ∈ A ⊓ omega1 P := by
    intro x
    rw [← hW]
    exact x.2
  have hWmap : W.map (h.xi : MulAut P).toMonoidHom = W := by
    rw [hW]
    rw [Subgroup.map_inf A (omega1 P) (h.xi : MulAut P).toMonoidHom (h.xi : MulAut P).injective,
      hA.2.1, map_xi_omega1 h]
  set ξW : MulAut ↥W :=
    (Subgroup.equivMapOfInjective W (h.xi : MulAut P).toMonoidHom
        (h.xi : MulAut P).injective).trans (MulEquiv.subgroupCongr hWmap) with hξW
  have h1 : ∀ x : ↥W, ((ξW x : ↥W) : P) = h.xi (x : P) := by
    intro x
    rw [hξW, MulEquiv.coe_trans, Function.comp_apply]
    exact Subgroup.coe_equivMapOfInjective_apply W (h.xi : MulAut P).toMonoidHom
      (h.xi : MulAut P).injective x
  have hcoe : ∀ (m : ℕ) (x : ↥W), (((ξW ^ m) x : ↥W) : P) = (h.xi ^ m) (x : P) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, h1, ih x]
  refine ⟨ξW, h1, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    have hxO : (x : P) ∈ omega1 P := (Subgroup.mem_inf.mp (hmem x)).2
    simpa [pow_two] using h.mem_omega1.mp hxO
  · intro a b ha hb
    have haO : (a : P) ∈ omega1 P := (Subgroup.mem_inf.mp (hmem a)).2
    have hbO : (b : P) ∈ omega1 P := (Subgroup.mem_inf.mp (hmem b)).2
    have ha1 : (a : P) ≠ 1 := fun hh => ha (Subtype.ext hh)
    have hb1 : (b : P) ≠ 1 := fun hh => hb (Subtype.ext hh)
    have ha2 : orderOf (a : P) = 2 := by
      have hdvd : orderOf (a : P) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using h.mem_omega1.mp haO)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) ha1
      · exact hh
    have hb2 : orderOf (b : P) = 2 := by
      have hdvd : orderOf (b : P) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using h.mem_omega1.mp hbO)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hb1
      · exact hh
    obtain ⟨k, hk⟩ := h.trans (a : P) (b : P) ha2 hb2
    exact ⟨k, Subtype.ext (by rw [hcoe k a]; exact hk)⟩

/-! ## Multiplicative form of the triviality of an alternating pairing -/

/-- Gorenstein–Thompson (Higman 1963, Lemma 4) in the form used below: on a finite elementary
abelian `2`-group on which `ξ` acts transitively away from `1`, every alternating `ξ`-equivariant
bi-additive self-pairing is trivial.  Commutativity is passed as a hypothesis rather than as a
typeclass instance. -/
theorem equivariant_bihom_trivial_comm {A : Type} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a * a = 1) (ξ : MulAut A)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξ ^ k) a = b)
    (c : A → A → A)
    (hmul : ∀ a b d : A, c (a * b) d = c a d * c b d)
    (hmul' : ∀ a b d : A, c a (b * d) = c a b * c a d)
    (halt : ∀ a : A, c a a = 1)
    (heq : ∀ a b : A, ξ (c a b) = c (ξ a) (ξ b)) :
    ∀ a b : A, c a b = 1 := by
  letI : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  exact equivariant_bihom_trivial h2 ξ htrans c hmul hmul' halt heq


/-! ## Higman 1963, Lemma 7 -/

/-- In a group in which `u`, `v`, `w` commute, `(u * v * w) ^ n = u ^ n * v ^ n * w ^ n`. -/
theorem mul_mul_pow_of_comm {G' : Type*} [Group G'] {u v w : G'}
    (huv : Commute u v) (huw : Commute u w) (hvw : Commute v w) (n : ℕ) :
    (u * v * w) ^ n = u ^ n * v ^ n * w ^ n := by
  rw [show u * v * w = (u * v) * w from rfl, (Commute.mul_left huw hvw).mul_pow,
    huv.mul_pow]

/-- The `2 ^ k`-th powers of the elements of `(⁅C,C⁆)²` are trivial, where `⁅C,C⁆ = A ^ (2 ^ s)`
and `2 ^ (s + 1 + k) = 2 ^ e`, `2 ^ e` being the exponent of `A`. -/
theorem pow_powSub_two_commutator_eq_one {A C : Subgroup P}
    (hAab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hCdA : ⁅C, C⁆ ≤ A)
    {s e k : ℕ} (hs : ⁅C, C⁆ = powSub A (2 ^ s))
    (hexp : ∀ x ∈ A, x ^ 2 ^ e = 1) (hsk : s + 1 + k = e) :
    ∀ ε ∈ powSub ⁅C, C⁆ 2, ε ^ 2 ^ k = 1 := by
  intro ε hε
  have hC'ab : ∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆, u * v = v * u :=
    fun u hu v hv => hAab u (hCdA hu) v (hCdA hv)
  obtain ⟨γ, hγ, hγε⟩ := (mem_powSub_iff hC'ab).mp hε
  have hγA : γ ∈ powSub A (2 ^ s) := hs ▸ hγ
  obtain ⟨a, ha, haγ⟩ := (mem_powSub_iff hAab).mp hγA
  rw [← hγε, ← haγ, ← pow_mul, ← pow_mul]
  have hpoweq : 2 ^ s * (2 * 2 ^ k) = 2 ^ e := by
    rw [mul_comm 2 (2 ^ k), ← pow_succ, ← pow_add, show s + (k + 1) = e from by omega]
  rw [hpoweq]
  exact hexp a ha

/-- **Higman 1963, Lemma 7.**  Let `A ≤ C` with `A` a `ξ`-invariant abelian normal subgroup of a
Suzuki 2-group and `C > A` a normal `ξ`-invariant cover of `A` (`C/A` a minimal normal
`ξ`-section).  If `Φ(C) = C²·⁅C,C⁆ = A` and `⁅C,C⁆ ≤ A²`, then `C` is abelian. -/
theorem higman_lemma7_general {A C : Subgroup P} (h : IsSuzuki2Grp P)
    (hA : IsXiAbelNormal h A) (hCn : C.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : powSub C 2 ⊔ ⁅C, C⁆ = A) (hCd : ⁅C, C⁆ ≤ powSub A 2) :
    ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
  classical
  have hAab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := hA.2.2
  have hAinv : A.map (h.xi : MulAut P).toMonoidHom = A := hA.2.1
  have hCdle : ⁅C, C⁆ ≤ A := hPhi ▸ le_sup_right
  have hC2le : powSub C 2 ≤ A := hPhi ▸ le_sup_left
  have hC'ab : ∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆, u * v = v * u :=
    fun u hu v hv => hAab u (hCdle hu) v (hCdle hv)
  rcases eq_or_ne A ⊥ with hAbot0 | hAbot
  · intro x hx y hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (by
      have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
        rw [← hAbot0]
        exact hCdle (Subgroup.commutator_mem_commutator hx hy)
      simpa using h1)
  · have hOm : omega1 P ≤ A := omega1_le_of_isXiAbelNormal_ne_bot h hA hAbot
    obtain ⟨e, hexp, hcard, hker, hstruct⟩ := homogeneous_structure h hAab hAinv
    have hinf : A ⊓ omega1 P = omega1 P := inf_eq_right.mpr hOm
    have hepos : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with he0 | hpos
      · exfalso
        have hA0 : A = ⊥ := by
          rw [Subgroup.eq_bot_iff_forall]
          intro x hx
          have h1 := hexp x hx
          rw [he0] at h1
          simpa using h1
        exact hAbot hA0
      · exact hpos
    have hkey := mem_powSub_two_iff_of_homogeneous hAab hepos hexp hcard
    have hCd_inv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨s, hs⟩ := hstruct ⁅C, C⁆ hCdle hCd_inv
    rcases eq_or_ne ⁅C, C⁆ ⊥ with hCd_bot | hCd_bot
    · intro x hx y hy
      exact commutatorElement_eq_one_iff_mul_comm.mp (by
        have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hCd_bot]
          exact Subgroup.commutator_mem_commutator hx hy
        simpa using h1)
    · have hsle : s ≤ e - 1 := by
        by_contra hcon
        have hes : e ≤ s := by omega
        exact hCd_bot (by rw [hs, powSub_eq_bot_of_exp hAab hes hexp])
      have hs1 : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h0 | hpos
        · exfalso
          subst h0
          have hCA' : ⁅C, C⁆ = A := by rw [hs, pow_zero, powSub_one_eq]
          have hAle : A ≤ powSub A 2 := hCA' ▸ hCd
          have hAeq : powSub A 2 = A := le_antisymm ((powSub_le (n := 2) (by norm_num))) hAle
          have hcardA : Nat.card ↥A = (Nat.card ↥(A ⊓ omega1 P)) ^ e := by
            have h0' := hcard 0 (Nat.zero_le e)
            rw [pow_zero, powSub_one_eq, Nat.sub_zero] at h0'
            exact h0'
          have hcardA2 : Nat.card ↥(powSub A 2) = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) := by
            have h1' := hcard 1 (by omega)
            rw [show (2 : ℕ) ^ 1 = 2 by norm_num] at h1'
            exact h1'
          have heq2 : (Nat.card ↥(A ⊓ omega1 P)) ^ e = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) := by
            rw [← hcardA, ← hcardA2, hAeq]
          have hq : Nat.card ↥(A ⊓ omega1 P) = 1 := by
            have h2 : (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) * Nat.card ↥(A ⊓ omega1 P)
                = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) * 1 := by
              rw [mul_one, ← pow_succ, show e - 1 + 1 = e from by omega]
              exact heq2
            exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos _) h2
          have hOm1 : Nat.card ↥(omega1 P) = 1 := by
            rw [← hinf]
            exact hq
          have := h.omega1_card_ge_four
          omega
        · exact hpos
      set k : ℕ := e - 1 - s with hkdef
      have hsk : s + 1 + k = e := by omega
      have hkpow : 2 ^ s * 2 ^ k = 2 ^ (e - 1) := by
        rw [← pow_add]; congr 1; omega
      -- ## commutator inclusions
      haveI hC'n : (⁅C, C⁆ : Subgroup P).Normal := Subgroup.commutator_normal _ _
      have hcommC : ⁅⁅C, C⁆, C⁆ ≤ powSub ⁅C, C⁆ 2 := by
        rw [Subgroup.commutator_le]
        intro u hu v hv
        have h1 : ⁅v, u⁆ ∈ powSub ⁅C, C⁆ 2 :=
          commutator_mem_powSub_two h ⟨hC'n, hCd_inv, hC'ab⟩ v u hu
        rw [show ⁅u, v⁆ = ⁅v, u⁆⁻¹ from by rw [commutatorElement_def]; group]
        exact (powSub ⁅C, C⁆ 2).inv_mem h1
      have hconjA : ∀ a ∈ A, ∀ m ∈ ⁅C, C⁆, a * m * a⁻¹ = m := by
        intro a ha m hm
        rw [hAab a ha m (hCdle hm), mul_assoc, mul_inv_cancel, mul_one]
      have hconjC : ∀ x ∈ C, ∀ m ∈ ⁅C, C⁆, x * m * x⁻¹ * m⁻¹ ∈ powSub ⁅C, C⁆ 2 := by
        intro x hx m hm
        have h1 : ⁅x, m⁆ ∈ powSub ⁅C, C⁆ 2 := by
          have h6 : ⁅m, x⁆ ∈ powSub ⁅C, C⁆ 2 :=
            hcommC (Subgroup.commutator_mem_commutator hm hx)
          rw [show ⁅x, m⁆ = ⁅m, x⁆⁻¹ from by rw [commutatorElement_def]; group]
          exact (powSub ⁅C, C⁆ 2).inv_mem h6
        have h2 : x * m * x⁻¹ * m⁻¹ = ⁅x, m⁆ := by rw [commutatorElement_def]
        rw [h2]
        exact h1
      have hC2C : ⁅powSub C 2, C⁆ ≤ powSub ⁅C, C⁆ 2 := by
        rw [Subgroup.commutator_le]
        intro d hd c' hc'
        rw [powSub] at hd
        induction hd using Subgroup.closure_induction with
        | mem d hd =>
            obtain ⟨x, hx, rfl⟩ := hd
            rw [pow_two, commutatorElement_mul_left_eq_conj_mul x x c']
            have h3 : ⁅x, c'⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hc'
            have h4 : x * ⁅x, c'⁆ * x⁻¹ * ⁅x, c'⁆⁻¹ ∈ powSub ⁅C, C⁆ 2 :=
              hconjC x hx ⁅x, c'⁆ h3
            have h6 : ⁅x, c'⁆ * ⁅x, c'⁆ ∈ powSub ⁅C, C⁆ 2 := by
              rw [← pow_two]
              exact pow_mem_powSub h3
            rw [show x * ⁅x, c'⁆ * x⁻¹ * ⁅x, c'⁆
                = (x * ⁅x, c'⁆ * x⁻¹ * ⁅x, c'⁆⁻¹) * (⁅x, c'⁆ * ⁅x, c'⁆) from by group]
            exact Subgroup.mul_mem _ h4 h6
        | one => simp
        | mul u v hu hv ihu ihv =>
            rw [commutatorElement_mul_left_eq_conj_mul u v c']
            have h4 : u * ⁅v, c'⁆ * u⁻¹ = ⁅v, c'⁆ :=
              hconjA u (hC2le hu) ⁅v, c'⁆ (((powSub_le (n := 2) (by norm_num))) ihv)
            rw [h4]
            exact Subgroup.mul_mem _ ihv ihu
        | inv u hu ihu =>
            rw [commutatorElement_inv_left]
            have hu' : ⁅c', u⁆ ∈ powSub ⁅C, C⁆ 2 := by
              rw [show ⁅c', u⁆ = ⁅u, c'⁆⁻¹ from by rw [commutatorElement_def]; group]
              exact (powSub ⁅C, C⁆ 2).inv_mem ihu
            have h4 : u⁻¹ * ⁅c', u⁆ * u = ⁅c', u⁆ := by
              simpa using hconjA u⁻¹ (A.inv_mem (hC2le hu)) ⁅c', u⁆
                ((powSub_le (n := 2) (by norm_num)) hu')
            rw [h4, show ⁅c', u⁆ = ⁅u, c'⁆⁻¹ from (commutatorElement_inv u c').symm]
            exact Subgroup.inv_mem _ ihu
      have hcommA : ⁅A, C⁆ ≤ powSub ⁅C, C⁆ 2 := by
        rw [Subgroup.commutator_le]
        intro a ha c' hc'
        rw [hPhi.symm] at ha
        obtain ⟨d, hd, m, hm, rfl⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := powSub C 2) (t := ⁅C, C⁆)).mp ha
        rw [commutatorElement_mul_left_eq_conj_mul d m c']
        have h5 : ⁅m, c'⁆ ∈ powSub ⁅C, C⁆ 2 := by
          have h6 : ⁅c', m⁆ ∈ powSub ⁅C, C⁆ 2 :=
            commutator_mem_powSub_two h ⟨hC'n, hCd_inv, hC'ab⟩ c' m hm
          rw [show ⁅m, c'⁆ = ⁅c', m⁆⁻¹ from by rw [commutatorElement_def]; group]
          exact (powSub ⁅C, C⁆ 2).inv_mem h6
        have h4 : d * ⁅m, c'⁆ * d⁻¹ = ⁅m, c'⁆ := hconjA d (hC2le hd) ⁅m, c'⁆
          (((powSub_le (n := 2) (by norm_num))) h5)
        rw [h4]
        exact Subgroup.mul_mem _ h5 (hC2C (Subgroup.commutator_mem_commutator hd hc'))
      have hkill : ∀ ε ∈ powSub ⁅C, C⁆ 2, ε ^ 2 ^ k = 1 :=
        pow_powSub_two_commutator_eq_one hAab hCdle hs hexp hsk
      -- ## the cover `φ : C → W` and the pairing
      set W : Subgroup P := powSub A (2 ^ (e - 1)) with hWdef
      have hWin : W = A ⊓ omega1 P := hWdef.trans hker
      have hWleA : W ≤ A := by rw [hWin]; exact inf_le_left
      obtain ⟨ξW, hξW, hWsq, hWtrans⟩ := exists_xiMulAut_inf_omega1 h hA hWin
      obtain ⟨hphi_hom, hphi_img, hphi_surj, hphi_ker, hphi_xi⟩ :=
        higman_lemma7_phi2 h hA hCn hCinv hAC hCA hcover hPhi hCd hAbot hepos hexp hkey hker
      have hmemW : ∀ w : ↥W, (w : P) ∈ A ⊓ omega1 P := by
        intro w; rw [← hWin]; exact w.2
      have hsurj : ∀ w : ↥W, ∃ x : P, x ∈ C ∧ x ^ 2 ^ e = (w : P) := fun w =>
        hphi_surj (w : P) (hmemW w)
      let rep : ↥W → P := fun w => Classical.choose (hsurj w)
      have rep_mem : ∀ w : ↥W, rep w ∈ C := fun w => (Classical.choose_spec (hsurj w)).1
      have rep_spec : ∀ w : ↥W, rep w ^ 2 ^ e = (w : P) :=
        fun w => (Classical.choose_spec (hsurj w)).2
      have hdiff : ∀ x y : P, x ∈ C → y ∈ C → x ^ 2 ^ e = y ^ 2 ^ e → x * y⁻¹ ∈ A := by
        intro x y hx hy hxy
        have hmem : x * y⁻¹ ∈ C := C.mul_mem hx (C.inv_mem hy)
        have h1 : (x * y⁻¹) ^ 2 ^ e = 1 := by
          rw [hphi_hom x hx y⁻¹ (C.inv_mem hy), inv_pow, hxy, mul_inv_cancel]
        exact (hphi_ker _ hmem).mp h1
      have hval : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ^ 2 ^ k ∈ W := by
        intro x hx y hy
        have h1 : ⁅x, y⁆ ∈ powSub A (2 ^ s) := by
          rw [← hs]
          exact Subgroup.commutator_mem_commutator hx hy
        obtain ⟨a, ha, hae⟩ := (mem_powSub_iff hAab).mp h1
        rw [← hae, ← pow_mul, hkpow]
        exact pow_mem_powSub ha
      -- ## the identities
      have hid1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x * y⁻¹ ∈ A →
          ⁅x, z⁆ ^ 2 ^ k = ⁅y, z⁆ ^ 2 ^ k := by
        intro x hx y hy z hz hxy
        obtain ⟨a, ha, hay⟩ : ∃ a ∈ A, x = a * y := ⟨x * y⁻¹, hxy, by group⟩
        have h2 : ⁅y, z⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hy hz
        rw [hay, commutatorElement_mul_left_eq_conj_mul a y z]
        have h7 : a * ⁅y, z⁆ * a⁻¹ = ⁅y, z⁆ := hconjA a ha ⁅y, z⁆ h2
        rw [show a * ⁅y, z⁆ * a⁻¹ * ⁅a, z⁆ = ⁅y, z⁆ * ⁅a, z⁆ from by
          rw [show a * ⁅y, z⁆ * a⁻¹ * ⁅a, z⁆ = (a * ⁅y, z⁆ * a⁻¹) * ⁅a, z⁆ from by group, h7]]
        have h1 : ⁅a, z⁆ ∈ powSub ⁅C, C⁆ 2 :=
          hcommA (Subgroup.commutator_mem_commutator ha hz)
        have h3 : Commute ⁅y, z⁆ ⁅a, z⁆ := by
          rw [Commute]
          exact hAab _ (hCdle h2) _ (hCdle (((powSub_le (n := 2) (by norm_num))) h1))
        rw [h3.mul_pow, hkill ⁅a, z⁆ h1, mul_one]
      have hid2 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x * y⁻¹ ∈ A →
          ⁅z, x⁆ ^ 2 ^ k = ⁅z, y⁆ ^ 2 ^ k := by
        intro x hx y hy z hz hxy
        obtain ⟨a, ha, hay⟩ : ∃ a ∈ A, x = a * y := ⟨x * y⁻¹, hxy, by group⟩
        have h2 : ⁅z, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hz hy
        rw [hay, commutatorElement_mul_right_eq_mul_conj z a y]
        have h7 : a * ⁅z, y⁆ * a⁻¹ = ⁅z, y⁆ := hconjA a ha ⁅z, y⁆ h2
        rw [show ⁅z, a⁆ * a * ⁅z, y⁆ * a⁻¹ = ⁅z, a⁆ * ⁅z, y⁆ from by
          rw [show ⁅z, a⁆ * a * ⁅z, y⁆ * a⁻¹ = ⁅z, a⁆ * (a * ⁅z, y⁆ * a⁻¹) from by group, h7]]
        have h1 : ⁅z, a⁆ ∈ powSub ⁅C, C⁆ 2 := by
          have h6 : ⁅a, z⁆ ∈ powSub ⁅C, C⁆ 2 :=
            hcommA (Subgroup.commutator_mem_commutator ha hz)
          rw [show ⁅z, a⁆ = ⁅a, z⁆⁻¹ from by rw [commutatorElement_def]; group]
          exact (powSub ⁅C, C⁆ 2).inv_mem h6
        have h3 : Commute ⁅z, a⁆ ⁅z, y⁆ := by
          rw [Commute]
          exact hAab _ (hCdle (((powSub_le (n := 2) (by norm_num))) h1)) _ (hCdle h2)
        rw [h3.mul_pow, hkill ⁅z, a⁆ h1, one_mul]
      have hid3 : ∀ x ∈ C, ∀ x' ∈ C, ∀ z ∈ C,
          ⁅x * x', z⁆ ^ 2 ^ k = ⁅x, z⁆ ^ 2 ^ k * ⁅x', z⁆ ^ 2 ^ k := by
        intro x hx x' hx' z hz
        have h2 : ⁅x', z⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx' hz
        have h3 : ⁅x, z⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hz
        rw [commutatorElement_mul_left_eq_conj_mul x x' z,
          show x * ⁅x', z⁆ * x⁻¹ * ⁅x, z⁆
              = (x * ⁅x', z⁆ * x⁻¹ * ⁅x', z⁆⁻¹) * (⁅x', z⁆ * ⁅x, z⁆) from by group]
        have hδ : (x * ⁅x', z⁆ * x⁻¹ * ⁅x', z⁆⁻¹) ∈ powSub ⁅C, C⁆ 2 := hconjC x hx ⁅x', z⁆ h2
        have hδC' : (x * ⁅x', z⁆ * x⁻¹ * ⁅x', z⁆⁻¹) ∈ ⁅C, C⁆ :=
          ((powSub_le (n := 2) (by norm_num))) hδ
        rw [show (x * ⁅x', z⁆ * x⁻¹ * ⁅x', z⁆⁻¹) * (⁅x', z⁆ * ⁅x, z⁆)
            = ((x * ⁅x', z⁆ * x⁻¹ * ⁅x', z⁆⁻¹) * ⁅x', z⁆) * ⁅x, z⁆ from by group]
        rw [mul_mul_pow_of_comm (hC'ab _ hδC' _ h2) (hC'ab _ hδC' _ h3) (hC'ab _ h2 _ h3)]
        rw [hkill _ hδ, one_mul]
        exact (hC'ab _ (Subgroup.pow_mem _ h2 _) _ (Subgroup.pow_mem _ h3 _))
      have hid4 : ∀ z ∈ C, ∀ x ∈ C, ∀ x' ∈ C,
          ⁅z, x * x'⁆ ^ 2 ^ k = ⁅z, x⁆ ^ 2 ^ k * ⁅z, x'⁆ ^ 2 ^ k := by
        intro z hz x hx x' hx'
        have h2 : ⁅z, x'⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hz hx'
        have h3 : ⁅z, x⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hz hx
        rw [commutatorElement_mul_right_eq_mul_conj z x x',
          show ⁅z, x⁆ * x * ⁅z, x'⁆ * x⁻¹
              = ⁅z, x⁆ * ((x * ⁅z, x'⁆ * x⁻¹ * ⁅z, x'⁆⁻¹) * ⁅z, x'⁆) from by group]
        have hδ : (x * ⁅z, x'⁆ * x⁻¹ * ⁅z, x'⁆⁻¹) ∈ powSub ⁅C, C⁆ 2 := hconjC x hx ⁅z, x'⁆ h2
        have hδC' : (x * ⁅z, x'⁆ * x⁻¹ * ⁅z, x'⁆⁻¹) ∈ ⁅C, C⁆ :=
          ((powSub_le (n := 2) (by norm_num))) hδ
        rw [show ⁅z, x⁆ * (x * ⁅z, x'⁆ * x⁻¹ * ⁅z, x'⁆⁻¹ * ⁅z, x'⁆)
            = (⁅z, x⁆ * (x * ⁅z, x'⁆ * x⁻¹ * ⁅z, x'⁆⁻¹)) * ⁅z, x'⁆ from by group]
        rw [mul_mul_pow_of_comm (hC'ab _ h3 _ hδC') (hC'ab _ h3 _ h2) (hC'ab _ hδC' _ h2)]
        rw [hkill _ hδ, mul_one]
      -- ## the pairing
      let c : ↥W → ↥W → ↥W := fun w w' =>
        ⟨⁅rep w, rep w'⁆ ^ 2 ^ k, hval (rep w) (rep_mem w) (rep w') (rep_mem w')⟩
      have hc_alt : ∀ w : ↥W, c w w = 1 := by
        intro w
        refine Subtype.ext ?_
        show ⁅rep w, rep w⁆ ^ 2 ^ k = (1 : P)
        rw [commutatorElement_self, one_pow]
      have hc_mul : ∀ w w' w'' : ↥W, c (w * w') w'' = c w w'' * c w' w'' := by
        intro w w' w''
        have hsame : rep (w * w') * (rep w * rep w')⁻¹ ∈ A := by
          refine hdiff _ _ (rep_mem _) (C.mul_mem (rep_mem w) (rep_mem w')) ?_
          rw [rep_spec (w * w'), hphi_hom (rep w) (rep_mem w) (rep w') (rep_mem w'),
            rep_spec w, rep_spec w']
          simp
        refine Subtype.ext ?_
        show ⁅rep (w * w'), rep w''⁆ ^ 2 ^ k = ⁅rep w, rep w''⁆ ^ 2 ^ k * ⁅rep w', rep w''⁆ ^ 2 ^ k
        rw [hid1 (rep (w * w')) (rep_mem _) (rep w * rep w')
            (C.mul_mem (rep_mem w) (rep_mem w')) (rep w'') (rep_mem _) hsame,
          hid3 (rep w) (rep_mem w) (rep w') (rep_mem w') (rep w'') (rep_mem w'')]
      have hc_mul' : ∀ w w' w'' : ↥W, c w (w' * w'') = c w w' * c w w'' := by
        intro w w' w''
        have hsame : rep (w' * w'') * (rep w' * rep w'')⁻¹ ∈ A := by
          refine hdiff _ _ (rep_mem _) (C.mul_mem (rep_mem w') (rep_mem w'')) ?_
          rw [rep_spec (w' * w''), hphi_hom (rep w') (rep_mem w') (rep w'') (rep_mem w''),
            rep_spec w', rep_spec w'']
          simp
        refine Subtype.ext ?_
        show ⁅rep w, rep (w' * w'')⁆ ^ 2 ^ k = ⁅rep w, rep w'⁆ ^ 2 ^ k * ⁅rep w, rep w''⁆ ^ 2 ^ k
        rw [hid2 (rep (w' * w'')) (rep_mem _) (rep w' * rep w'')
            (C.mul_mem (rep_mem w') (rep_mem w'')) (rep w) (rep_mem w) hsame,
          hid4 (rep w) (rep_mem w) (rep w') (rep_mem w') (rep w'') (rep_mem w'')]
      have hxiC : ∀ z ∈ C, h.xi z ∈ C := by
        intro z hz
        have hmem := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) hz
        rwa [hCinv] at hmem
      have hc_eq : ∀ w w' : ↥W, ξW (c w w') = c (ξW w) (ξW w') := by
        intro w w'
        have hs1 : rep (ξW w) * (h.xi (rep w))⁻¹ ∈ A := by
          refine hdiff _ _ (rep_mem _) (hxiC _ (rep_mem w)) ?_
          rw [rep_spec (ξW w), hξW w, hphi_xi (rep w) (rep_mem w), ← rep_spec w]
        have hs2 : rep (ξW w') * (h.xi (rep w'))⁻¹ ∈ A := by
          refine hdiff _ _ (rep_mem _) (hxiC _ (rep_mem w')) ?_
          rw [rep_spec (ξW w'), hξW w', hphi_xi (rep w') (rep_mem w'), ← rep_spec w']
        refine Subtype.ext ?_
        show ((ξW (c w w') : ↥W) : P) = (c (ξW w) (ξW w') : P)
        rw [hξW (c w w')]
        simp only [c]
        rw [map_pow, map_commutatorElement,
          ← hid1 (rep (ξW w)) (rep_mem _) (h.xi (rep w)) (hxiC _ (rep_mem w))
            (h.xi (rep w')) (hxiC _ (rep_mem w')) hs1,
          ← hid2 (rep (ξW w')) (rep_mem _) (h.xi (rep w')) (hxiC _ (rep_mem w'))
            (rep (ξW w)) (rep_mem _) hs2]
      have htriv_c : ∀ w w' : ↥W, c w w' = 1 :=
        equivariant_bihom_trivial_comm (fun x y => Subtype.ext (hAab x (hWleA x.2) y (hWleA y.2)))
          hWsq ξW hWtrans c hc_mul hc_mul' hc_alt hc_eq
      -- ## conclusion: `⁅C,C⁆` has exponent `2 ^ k`, hence is trivial
      have htriv : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ^ 2 ^ k = 1 := by
        intro x hx y hy
        have hxW : x ^ 2 ^ e ∈ W := by rw [hWin]; exact hphi_img x hx
        have hyW : y ^ 2 ^ e ∈ W := by rw [hWin]; exact hphi_img y hy
        have hdx : rep ⟨x ^ 2 ^ e, hxW⟩ * x⁻¹ ∈ A := by
          refine hdiff (rep ⟨x ^ 2 ^ e, hxW⟩) x (rep_mem _) hx ?_
          rw [rep_spec]
        have hdy : rep ⟨y ^ 2 ^ e, hyW⟩ * y⁻¹ ∈ A := by
          refine hdiff (rep ⟨y ^ 2 ^ e, hyW⟩) y (rep_mem _) hy ?_
          rw [rep_spec]
        have hzero : ⁅rep ⟨x ^ 2 ^ e, hxW⟩, rep ⟨y ^ 2 ^ e, hyW⟩⁆ ^ 2 ^ k = 1 := by
          have h1 := htriv_c ⟨x ^ 2 ^ e, hxW⟩ ⟨y ^ 2 ^ e, hyW⟩
          have h2 : ((c ⟨x ^ 2 ^ e, hxW⟩ ⟨y ^ 2 ^ e, hyW⟩ : ↥W) : P) = 1 := by
            rw [h1]
            rfl
          simpa only [c] using h2
        rw [← hid2 (rep ⟨y ^ 2 ^ e, hyW⟩) (rep_mem _) y hy x hx hdy,
          ← hid1 (rep ⟨x ^ 2 ^ e, hxW⟩) (rep_mem _) x hx
            (rep ⟨y ^ 2 ^ e, hyW⟩) (rep_mem _) hdx]
        exact hzero
      have hbot : powSub ⁅C, C⁆ (2 ^ k) = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro z hz
        rw [mem_powSub_iff hC'ab] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        rw [← hwz]
        have hgen : ∀ u ∈ ⁅C, C⁆, u ^ 2 ^ k = 1 := by
          intro u hu
          induction hu using Subgroup.closure_induction with
          | mem u hu =>
              obtain ⟨x, hx, y, hy, rfl⟩ := hu
              exact htriv x hx y hy
          | one => simp
          | mul u v hu hv ihu ihv =>
              have hc : Commute u v := hC'ab u hu v hv
              rw [hc.mul_pow, ihu, ihv, mul_one]
          | inv u hu ihu => rw [inv_pow, ihu, inv_one]
        exact hgen w hw
      have hnothing : powSub (powSub A (2 ^ s)) (2 ^ k) = powSub A (2 ^ (e - 1)) := by
        rw [powSub_powSub hAab, hkpow]
      have hA2bot : powSub A (2 ^ (e - 1)) = ⊥ := by
        rw [← hnothing, ← hs]
        exact hbot
      have hOmbot : omega1 P = ⊥ := ((hker.trans hinf).symm) ▸ hA2bot
      have hOm_ne : omega1 P ≠ ⊥ := by
        intro hb
        have hcard : Nat.card ↥(omega1 P) = 1 := by rw [hb]; simp
        have := h.omega1_card_ge_four
        omega
      exact (hOm_ne hOmbot).elim

/-! ## Higman's endgame: a maximal `ξ`-invariant abelian normal subgroup of exponent `≤ 4`
contains `Φ(P)` -/

/-- **Higman 1963, Lemma 9, second part.**  If `A` is a maximal `ξ`-invariant abelian normal
subgroup of a Suzuki 2-group with `powSub A 4 = ⊥`, then `Φ(P) = P²·[P,P] ≤ A`.

Take a minimal `ξ`-invariant normal cover `C > A` with `C ≤ A·Φ(P)`; then `C ≤ C_P(A)`
(`Φ(P)` centralizes `A` when `A⁴ = ⊥`).  `Φ(C) ≤ A` and `A² ≤ Φ(C)`, so `Φ(C) = A²` or `= A`.
In the first case Higman's Lemma 2 gives an immediate contradiction; in the second, `⁅C,C⁆ ≤ Ω₁`
(class two) and `⁅C,C⁆ = A ^ (2 ^ j)`: `A⁴ = ⊥` forces `e ≤ 2`, so either `C` is abelian
(contradicting maximality) or `⁅C,C⁆ = Ω₁` and the alternating commutator pairing
`C/A × C/A → Ω₁` with `C/A ≅ Ω₁` contradicts Gorenstein–Thompson (Lemma 4). -/
theorem frattini_le_of_maximal {A : Subgroup P} (h : IsSuzuki2Grp P)
    (hA : IsXiAbelNormal h A) (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (h4 : powSub A 4 = ⊥) :
    powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A := by
  classical
  by_contra hle
  have hAn : A.Normal := hA.1
  have hAinv : A.map (h.xi : MulAut P).toMonoidHom = A := hA.2.1
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.2.2
  have hOm : omega1 P ≤ A := omega1_le_of_maximal h hA hmax
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : omega1 P ≤ (⊥ : Subgroup P) := hbot ▸ hOm
    have hcard : Nat.card ↥(omega1 P) = 1 := by
      rw [le_bot_iff.mp h1]
      simp
    have := h.omega1_card_ge_four
    omega
  have hPhic : powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤
      Subgroup.centralizer (A : Set P) := MSA.commutator_frattini_centralizes (h := h) hA h4
  set Φ : Subgroup P := powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ with hΦ
  have htopinv : (⊤ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective
  have hpow_top : ∀ φ : MulAut P, (⊤ : Subgroup P).map (φ : MulAut P).toMonoidHom = ⊤ :=
    fun φ => Subgroup.map_top_of_surjective _ φ.surjective
  have hpow_n : (powSub (⊤ : Subgroup P) 2).Normal :=
    (Subgroup.normal_iff_map_conj_eq).mpr fun g => map_powSub (MulAut.conj g) (hpow_top _) 2
  have hcom_n : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).Normal := Subgroup.commutator_normal _ _
  haveI : (powSub (⊤ : Subgroup P) 2).Normal := hpow_n
  haveI : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).Normal := hcom_n
  haveI : Φ.Normal := hΦ ▸ Subgroup.sup_normal _ _
  have hΦinv : Φ.map (h.xi : MulAut P).toMonoidHom = Φ := by
    rw [hΦ, Subgroup.map_sup, map_powSub (h.xi : MulAut P) htopinv 2, Subgroup.map_commutator,
      htopinv]
  have hMA : A ⊔ Φ ≠ A := fun hEq => hle (hEq ▸ le_sup_right)
  obtain ⟨C, hCn, hCinv, hAC, hCM, hCA, hcover⟩ :=
    MSA.exists_minimal_covering h (A := A) (M := A ⊔ Φ) (Subgroup.sup_normal A Φ)
      (by rw [Subgroup.map_sup, hAinv, hΦinv]) le_sup_left hMA
  have hAcent : A ≤ Subgroup.centralizer (A : Set P) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hAab y hy x hx
  have hCcent : C ≤ Subgroup.centralizer (A : Set P) := hCM.trans (sup_le hAcent hPhic)
  have hPhiC_le : powSub C 2 ⊔ ⁅C, C⁆ ≤ A :=
    MSA.phi_le_of_minimal_covering h hAn hAinv hCn hCinv hAC (Ne.symm hCA) hcover
  have hA2_le : powSub A 2 ≤ powSub C 2 ⊔ ⁅C, C⁆ :=
    (powSub_mono (n := 2) hAC).trans le_sup_left
  have hPhiC_inv : (powSub C 2 ⊔ ⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom
      = powSub C 2 ⊔ ⁅C, C⁆ := by
    rw [Subgroup.map_sup, map_powSub (h.xi : MulAut P) hCinv 2, Subgroup.map_commutator, hCinv]
  rcases xi_invariant_eq_powSub_two_or_self h hA hPhiC_le hA2_le hPhiC_inv with hPhiC | hPhiC
  · -- `Φ(C) = A²`: contradiction with Higman's Lemma 2
    obtain ⟨b, hbC, hbA⟩ := exists_mem_notMem_of_ne hAC (Ne.symm hCA)
    have hb2 : b ^ 2 ∈ powSub A 2 := by
      have h1 : b ^ 2 ∈ powSub C 2 := pow_mem_powSub (n := 2) hbC
      rw [← hPhiC]
      exact (le_sup_left : powSub C 2 ≤ powSub C 2 ⊔ ⁅C, C⁆) h1
    have hbcomm : ∀ a ∈ A, ⁅b, a⁆ ∈ powSub A 4 := by
      intro a ha
      rw [commutator_eq_one_of_mem_centralizer hCcent hbC ha]
      exact Subgroup.one_mem _
    exact higman_lemma2 h hA hOm hAne hbA ⟨hb2, hbcomm⟩
  · -- `Φ(C) = A`
    have hC2le : powSub C 2 ≤ A := hPhiC ▸ le_sup_left
    have hCdle : ⁅C, C⁆ ≤ A := hPhiC ▸ le_sup_right
    have hCd_om : ⁅C, C⁆ ≤ omega1 P :=
      commutator_le_omega1_of_le_centralizer h hAC hCcent hC2le hCdle
    obtain ⟨e, hexp, hcard, hker, hstruct⟩ := homogeneous_structure h hAab hAinv
    have hinf : A ⊓ omega1 P = omega1 P := inf_eq_right.mpr hOm
    have he2 : e ≤ 2 := by
      rcases Nat.lt_or_ge e 2 with hlt | hge
      · omega
      · have hc := hcard 2 hge
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, h4, hinf, Subgroup.card_bot] at hc
        have hq : Nat.card ↥(omega1 P) ≠ 1 := by
          have := h.omega1_card_ge_four
          omega
        have hz : e - 2 = 0 := (Nat.pow_eq_one.mp hc.symm).resolve_left hq
        omega
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    · exfalso
      have hA0 : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have h1 := hexp x hx
        rw [he0] at h1
        simpa using h1
      exact hAne hA0
    · have hkey := mem_powSub_two_iff_of_homogeneous hAab hepos hexp hcard
      by_cases hCd_bot : ⁅C, C⁆ = ⊥
      · -- `C` is abelian, contradicting maximality
        have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
          intro x hx y hy
          exact commutatorElement_eq_one_iff_mul_comm.mp (by
            have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
              rw [← hCd_bot]
              exact Subgroup.commutator_mem_commutator hx hy
            simpa using h1)
        exact hCA (hmax C ⟨hCn, hCinv, hcomm⟩ hAC)
      · -- `⁅C,C⁆ = Ω₁`
        have hOmeq : omega1 P = powSub A (2 ^ (e - 1)) := (hker.trans hinf).symm
        have hCdeq : ⁅C, C⁆ = omega1 P := by
          have hinv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
            rw [Subgroup.map_commutator, hCinv]
          obtain ⟨j, hj⟩ := hstruct ⁅C, C⁆ hCdle hinv
          have hjle : j ≤ e - 1 := by
            by_contra hcon
            have hes : e ≤ j := by omega
            exact hCd_bot (by rw [hj, powSub_eq_bot_of_exp hAab hes hexp])
          have hle1 : powSub A (2 ^ (e - 1)) ≤ powSub A (2 ^ j) :=
            powSub_le_of_dvd hAab (Nat.pow_dvd_pow 2 hjle)
          exact le_antisymm hCd_om (by rw [hj, hOmeq]; exact hle1)
        rcases (show e = 1 ∨ e = 2 by omega) with he1 | he2'
        · -- `e = 1`: `A = Ω₁(P)` is the unique nontrivial abelian normal `ξ`-subgroup, so `P`
          -- has class two and `Φ(P) ≤ Z(P) = A`
          exfalso
          have hAeqOm : A = omega1 P := by
            have hh := hker
            rw [he1, show (2 : ℕ) ^ (1 - 1) = 1 by norm_num, powSub_one_eq] at hh
            rwa [hinf] at hh
          have hZeq : Subgroup.center P = A :=
            le_antisymm (center_le_of_maximal h hA hmax) (hAeqOm ▸ h.omega1_le_center)
          have huniq : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
              (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → B ≠ ⊥ → B = A := by
            intro B hBn hBinv hBab hBne
            have hOmB : omega1 P ≤ B :=
              omega1_le_of_isXiAbelNormal_ne_bot h ⟨hBn, hBinv, hBab⟩ hBne
            exact hmax B ⟨hBn, hBinv, hBab⟩ (by rw [hAeqOm]; exact hOmB)
          have hcls : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ :=
            lowerCentralSeries_two_eq_bot_of_unique_abelian_normal h huniq
          have hDcenter : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := by
            rw [← Subgroup.commutator_top_right_eq_bot_iff_le_center]
            have h2 : ⁅(⊤ : Subgroup P).lowerCentralSeries 1, (⊤ : Subgroup P)⁆ = ⊥ := by
              rw [← Subgroup.lowerCentralSeries_succ]
              exact hcls
            simpa using h2
          have hD_om : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P := (hZeq.trans hAeqOm) ▸ hDcenter
          have hsq_center : ∀ x : P, x ^ 2 ∈ Subgroup.center P :=
            fun x => sq_mem_center_of_comm h hD_om x
          have hZO : omega1 P = Subgroup.center P := (hZeq.trans hAeqOm).symm
          have hP2A : powSub (⊤ : Subgroup P) 2 ≤ A := by
            rw [powSub, Subgroup.closure_le]
            rintro y ⟨x, -, rfl⟩
            rw [hAeqOm, hZO]
            exact hsq_center x
          exact hle (sup_le hP2A (hZeq ▸ hDcenter))
        · -- `e = 2`: the commutator pairing `C/A × C/A → Ω₁`
          exfalso
          have hA2eq : powSub A 2 = omega1 P := by
            have hh := hker
            rw [he2', show (2 : ℕ) ^ (2 - 1) = 2 by norm_num] at hh
            rwa [hinf] at hh
          have hCd2 : ⁅C, C⁆ ≤ powSub A 2 := by rw [hCdeq, hA2eq]
          set W : Subgroup P := powSub A (2 ^ (e - 1)) with hWdef
          have hWin : W = A ⊓ omega1 P := hWdef.trans hker
          have hWleA : W ≤ A := by rw [hWin]; exact inf_le_left
          obtain ⟨ξW, hξW, hWsq, hWtrans⟩ := exists_xiMulAut_inf_omega1 h hA hWin
          obtain ⟨hphi_hom, hphi_img, hphi_surj, hphi_ker, hphi_xi⟩ :=
            higman_lemma7_phi2 h hA hCn hCinv hAC (Ne.symm hCA) hcover hPhiC hCd2 hAne hepos
              hexp hkey hker
          have hmemW : ∀ w : ↥W, (w : P) ∈ A ⊓ omega1 P := by
            intro w
            rw [← hWin]
            exact w.2
          have hsurj : ∀ w : ↥W, ∃ x : P, x ∈ C ∧ x ^ 2 ^ e = (w : P) := fun w =>
            hphi_surj (w : P) (hmemW w)
          let rep : ↥W → P := fun w => Classical.choose (hsurj w)
          have rep_mem : ∀ w : ↥W, rep w ∈ C := fun w => (Classical.choose_spec (hsurj w)).1
          have rep_spec : ∀ w : ↥W, rep w ^ 2 ^ e = (w : P) :=
            fun w => (Classical.choose_spec (hsurj w)).2
          have hdiff : ∀ x y : P, x ∈ C → y ∈ C → x ^ 2 ^ e = y ^ 2 ^ e → x * y⁻¹ ∈ A := by
            intro x y hx hy hxy
            have hmem : x * y⁻¹ ∈ C := C.mul_mem hx (C.inv_mem hy)
            have h1 : (x * y⁻¹) ^ 2 ^ e = 1 := by
              rw [hphi_hom x hx y⁻¹ (C.inv_mem hy), inv_pow, hxy, mul_inv_cancel]
            exact (hphi_ker _ hmem).mp h1
          have hval : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ W := by
            intro x hx y hy
            have h1 : ⁅x, y⁆ ∈ omega1 P := by
              rw [← hCdeq]
              exact Subgroup.commutator_mem_commutator hx hy
            have h2 : ⁅x, y⁆ ∈ A ⊓ omega1 P := by
              rw [hinf]
              exact h1
            rwa [← hWin] at h2
          have hid1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x * y⁻¹ ∈ A → ⁅x, z⁆ = ⁅y, z⁆ := by
            intro x hx y hy z hz hxy
            obtain ⟨a, ha, hay⟩ : ∃ a ∈ A, x = a * y :=
              ⟨x * y⁻¹, hxy, by group⟩
            have hza1 : ⁅a, z⁆ = 1 :=
              commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp (hCcent hz) a ha)
            have hcent : ⁅y, z⁆ ∈ Subgroup.center P :=
              h.omega1_le_center (by rw [← hCdeq]; exact Subgroup.commutator_mem_commutator hy hz)
            rw [hay, commutatorElement_mul_left_eq_conj_mul a y z, hza1, mul_one,
              Subgroup.mem_center_iff.mp hcent a, mul_assoc, mul_inv_cancel, mul_one]
          have hid2 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x * y⁻¹ ∈ A → ⁅z, x⁆ = ⁅z, y⁆ := by
            intro x hx y hy z hz hxy
            obtain ⟨a, ha, hay⟩ : ∃ a ∈ A, x = a * y :=
              ⟨x * y⁻¹, hxy, by group⟩
            have haz1 : ⁅z, a⁆ = 1 := commutator_eq_one_of_mem_centralizer hCcent hz ha
            have hcent : ⁅z, y⁆ ∈ Subgroup.center P :=
              h.omega1_le_center (by rw [← hCdeq]; exact Subgroup.commutator_mem_commutator hz hy)
            rw [hay, commutatorElement_mul_right_eq_mul_conj z a y, haz1, one_mul,
              Subgroup.mem_center_iff.mp hcent a, mul_assoc, mul_inv_cancel, mul_one]
          have hid3 : ∀ x ∈ C, ∀ x' ∈ C, ∀ z ∈ C,
              ⁅x * x', z⁆ = ⁅x, z⁆ * ⁅x', z⁆ := by
            intro x hx x' hx' z hz
            have hcent : ⁅x', z⁆ ∈ Subgroup.center P :=
              h.omega1_le_center (by rw [← hCdeq]; exact Subgroup.commutator_mem_commutator hx' hz)
            have hcent2 : ⁅x, z⁆ ∈ Subgroup.center P :=
              h.omega1_le_center (by rw [← hCdeq]; exact Subgroup.commutator_mem_commutator hx hz)
            rw [commutatorElement_mul_left_eq_conj_mul x x' z]
            have h1 : x * ⁅x', z⁆ * x⁻¹ = ⁅x', z⁆ := by
              rw [Subgroup.mem_center_iff.mp hcent x, mul_assoc, mul_inv_cancel, mul_one]
            rw [h1, Subgroup.mem_center_iff.mp hcent2 ⁅x', z⁆]
          have hid4 : ∀ z ∈ C, ∀ x ∈ C, ∀ x' ∈ C,
              ⁅z, x * x'⁆ = ⁅z, x⁆ * ⁅z, x'⁆ := by
            intro z hz x hx x' hx'
            have hcent2 : ⁅z, x'⁆ ∈ Subgroup.center P :=
              h.omega1_le_center (by rw [← hCdeq]; exact Subgroup.commutator_mem_commutator hz hx')
            rw [commutatorElement_mul_right_eq_mul_conj z x x']
            have h1 : x * ⁅z, x'⁆ * x⁻¹ = ⁅z, x'⁆ := by
              rw [Subgroup.mem_center_iff.mp hcent2 x, mul_assoc, mul_inv_cancel, mul_one]
            rw [show ⁅z, x⁆ * x * ⁅z, x'⁆ * x⁻¹ = ⁅z, x⁆ * (x * ⁅z, x'⁆ * x⁻¹) from by group,
              h1]
          let c : ↥W → ↥W → ↥W := fun w w' =>
            ⟨⁅rep w, rep w'⁆, hval (rep w) (rep_mem w) (rep w') (rep_mem w')⟩
          have hc_alt : ∀ w : ↥W, c w w = 1 := fun w =>
            Subtype.ext (by simp [c, commutatorElement_self])
          have hc_mul : ∀ w w' w'' : ↥W, c (w * w') w'' = c w w'' * c w' w'' := by
            intro w w' w''
            have hsame : rep (w * w') * (rep w * rep w')⁻¹ ∈ A := by
              refine hdiff _ _ (rep_mem _) (C.mul_mem (rep_mem w) (rep_mem w')) ?_
              rw [rep_spec (w * w'), hphi_hom (rep w) (rep_mem w) (rep w') (rep_mem w'),
                rep_spec w, rep_spec w']
              simp
            refine Subtype.ext ?_
            show ⁅rep (w * w'), rep w''⁆ = ⁅rep w, rep w''⁆ * ⁅rep w', rep w''⁆
            rw [hid1 (rep (w * w')) (rep_mem _) (rep w * rep w')
                (C.mul_mem (rep_mem w) (rep_mem w')) (rep w'') (rep_mem _) hsame,
              hid3 (rep w) (rep_mem w) (rep w') (rep_mem w') (rep w'') (rep_mem w'')]
          have hc_mul' : ∀ w w' w'' : ↥W, c w (w' * w'') = c w w' * c w w'' := by
            intro w w' w''
            have hsame : rep (w' * w'') * (rep w' * rep w'')⁻¹ ∈ A := by
              refine hdiff _ _ (rep_mem _) (C.mul_mem (rep_mem w') (rep_mem w'')) ?_
              rw [rep_spec (w' * w''), hphi_hom (rep w') (rep_mem w') (rep w'') (rep_mem w''),
                rep_spec w', rep_spec w'']
              simp
            refine Subtype.ext ?_
            show ⁅rep w, rep (w' * w'')⁆ = ⁅rep w, rep w'⁆ * ⁅rep w, rep w''⁆
            rw [hid2 (rep (w' * w'')) (rep_mem _) (rep w' * rep w'')
                (C.mul_mem (rep_mem w') (rep_mem w'')) (rep w) (rep_mem w) hsame,
              hid4 (rep w) (rep_mem w) (rep w') (rep_mem w') (rep w'') (rep_mem w'')]
          have hxiC : ∀ z ∈ C, h.xi z ∈ C := by
            intro z hz
            have hmem := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) hz
            rwa [hCinv] at hmem
          have hc_eq : ∀ w w' : ↥W, ξW (c w w') = c (ξW w) (ξW w') := by
            intro w w'
            have hs1 : rep (ξW w) * (h.xi (rep w))⁻¹ ∈ A := by
              refine hdiff _ _ (rep_mem _) (hxiC _ (rep_mem w)) ?_
              rw [rep_spec (ξW w), hξW w, hphi_xi (rep w) (rep_mem w), ← rep_spec w]
            have hs2 : rep (ξW w') * (h.xi (rep w'))⁻¹ ∈ A := by
              refine hdiff _ _ (rep_mem _) (hxiC _ (rep_mem w')) ?_
              rw [rep_spec (ξW w'), hξW w', hphi_xi (rep w') (rep_mem w'), ← rep_spec w']
            refine Subtype.ext ?_
            show ((ξW (c w w') : ↥W) : P) = (c (ξW w) (ξW w') : P)
            rw [hξW (c w w')]
            show h.xi ⁅rep w, rep w'⁆ = ⁅rep (ξW w), rep (ξW w')⁆
            rw [map_commutatorElement,
              ← hid1 (rep (ξW w)) (rep_mem _) (h.xi (rep w)) (hxiC _ (rep_mem w))
                (h.xi (rep w')) (hxiC _ (rep_mem w')) hs1,
              ← hid2 (rep (ξW w')) (rep_mem _) (h.xi (rep w')) (hxiC _ (rep_mem w'))
                (rep (ξW w)) (rep_mem _) hs2]
          have htriv_c : ∀ w w' : ↥W, c w w' = 1 :=
            equivariant_bihom_trivial_comm
              (fun x y => Subtype.ext (hAab x (hWleA x.2) y (hWleA y.2)))
              hWsq ξW hWtrans c hc_mul hc_mul' hc_alt hc_eq
          have htriv : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ = 1 := by
            intro x hx y hy
            have hxW : x ^ 2 ^ e ∈ W := by
              rw [hWin]
              exact hphi_img x hx
            have hyW : y ^ 2 ^ e ∈ W := by
              rw [hWin]
              exact hphi_img y hy
            have hdx : rep ⟨x ^ 2 ^ e, hxW⟩ * x⁻¹ ∈ A := by
              refine hdiff _ _ (rep_mem _) hx ?_
              rw [rep_spec]
            have hdy : rep ⟨y ^ 2 ^ e, hyW⟩ * y⁻¹ ∈ A := by
              refine hdiff _ _ (rep_mem _) hy ?_
              rw [rep_spec]
            have hzero : ⁅rep ⟨x ^ 2 ^ e, hxW⟩, rep ⟨y ^ 2 ^ e, hyW⟩⁆ = 1 := by
              have h1 := htriv_c ⟨x ^ 2 ^ e, hxW⟩ ⟨y ^ 2 ^ e, hyW⟩
              have h2 : ((c ⟨x ^ 2 ^ e, hxW⟩ ⟨y ^ 2 ^ e, hyW⟩ : ↥W) : P) = 1 := by
                rw [h1]
                rfl
              simpa only [c] using h2
            rw [← hid2 (rep ⟨y ^ 2 ^ e, hyW⟩) (rep_mem _) y hy x hx hdy,
              ← hid1 (rep ⟨x ^ 2 ^ e, hxW⟩) (rep_mem _) x hx
                (rep ⟨y ^ 2 ^ e, hyW⟩) (rep_mem _) hdx]
            exact hzero
          have hbot : ⁅C, C⁆ = ⊥ := by
            rw [← le_bot_iff]
            exact Subgroup.commutator_le.mpr htriv
          have hOm_ne : omega1 P ≠ ⊥ := by
            intro hb
            have hcard : Nat.card ↥(omega1 P) = 1 := by rw [hb]; simp
            have := h.omega1_card_ge_four
            omega
          exact hOm_ne (hCdeq ▸ hbot)

/-- Conjugation by a central element is trivial. -/
private lemma mul_conj_cancel {G : Type} [Group G] {z x : G} (h : z * x = x * z) :
    z * x * z⁻¹ = x := by rw [h]; group

/-- **Higman 1963, Lemma 3, final step** (local form).  `A` is a `ξ`-invariant abelian normal
subgroup of a Suzuki 2-group with `Ω₁(P) ≤ A`; `u ∈ C ∖ A` with `C² ≤ A²` and `ξ u ∈ u A`.
Contradiction.

NB: renamed from `higman_lemma3_final_step` because that name is taken by the (different!)
theorem of `Submission/Work/Higman/higman_lemma3_final_step.lean`; two declarations of the same
name in `Work.Higman` made the two import chains mutually unimportable. -/
theorem higman_lemma3_final_step_local (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hOm : omega1 P ≤ A)
    (hC2 : powSub C 2 ≤ powSub A 2) {u : P} (huC : u ∈ C) (huA : u ∉ A)
    (htriv : h.xi u * u⁻¹ ∈ A) : False := by
  classical
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : omega1 P ≤ (⊥ : Subgroup P) := hbot ▸ hOm
    have h2 : Nat.card ↥(omega1 P) = 1 := by rw [le_bot_iff.mp h1]; simp
    have h3 := h.omega1_card_ge_four
    omega
  obtain ⟨D⟩ := exists_homocyclicData h hA
  obtain ⟨a0, ha0A, ha0ord⟩ := D.horder
  have hu2A : u * u ∈ A := by
    have h1 : u * u ∈ powSub C 2 := by
      rw [← pow_two]; exact pow_mem_powSub (A := C) (n := 2) huC
    exact powSub_le (A := A) (n := 2) (by norm_num) (hC2 h1)
  -- `c = u⁻¹ ξ u ∈ A` and `ξ u = u c`
  set c : P := u⁻¹ * h.xi u with hcdef
  have hcA : c ∈ A := by
    have h1 : u⁻¹ * (h.xi u * u⁻¹) * u ∈ A := by
      simpa [inv_inv] using hAn.conj_mem (h.xi u * u⁻¹) htriv u⁻¹
    have h2 : u⁻¹ * (h.xi u * u⁻¹) * u = c := by rw [hcdef]; group
    rwa [h2] at h1
  have hxiu : h.xi u = u * c := by rw [hcdef]; group
  letI hAcomm : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun x y => Subtype.ext (hAb x x.2 y y.2) }
  letI : DivInvMonoid ↥A := (inferInstance : Group ↥A).toDivInvMonoid
  letI : Monoid ↥A := (inferInstance : Group ↥A).toMonoid
  -- the `ξ`-action on `A`
  let xA : ↥A ≃* ↥A :=
    { toFun := fun a => ⟨h.xi (a : P), by
        have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
        rwa [hA.map_eq] at hm⟩
      invFun := fun a => ⟨(h.xi : MulAut P).symm (a : P), symm_mem_of_map_eq h.xi hA.map_eq a.2⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun a => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have xA_coe : ∀ a : ↥A, ((xA a : ↥A) : P) = h.xi (a : P) := fun a => rfl
  -- conjugation defects for `u` and for `ξ u`
  let delu : ↥A → ↥A := fun a => ⟨u⁻¹ * (a : P) * u * (a : P)⁻¹, by
    have h1 : u⁻¹ * (a : P) * u ∈ A := by simpa [inv_inv] using hAn.conj_mem (a : P) a.2 u⁻¹
    exact A.mul_mem h1 (A.inv_mem a.2)⟩
  have delu_coe : ∀ a : ↥A, ((delu a : ↥A) : P) = u⁻¹ * (a : P) * u * (a : P)⁻¹ := fun a => rfl
  have delu_mul : ∀ a b : ↥A, delu (a * b) = delu a * delu b := by
    intro a b
    refine Subtype.ext ?_
    simp only [delu_coe, Subgroup.coe_mul]
    exact delta_mul h hA u a b
  let delv : ↥A → ↥A := fun a => ⟨(h.xi u)⁻¹ * (a : P) * (h.xi u) * (a : P)⁻¹, by
    have h1 : (h.xi u)⁻¹ * (a : P) * (h.xi u) ∈ A := by
      simpa [inv_inv] using hAn.conj_mem (a : P) a.2 (h.xi u)⁻¹
    exact A.mul_mem h1 (A.inv_mem a.2)⟩
  have delv_coe : ∀ a : ↥A,
      ((delv a : ↥A) : P) = (h.xi u)⁻¹ * (a : P) * (h.xi u) * (a : P)⁻¹ := fun a => rfl
  have delv_mul : ∀ a b : ↥A, delv (a * b) = delv a * delv b := by
    intro a b
    refine Subtype.ext ?_
    simp only [delv_coe, Subgroup.coe_mul]
    exact delta_mul h hA (h.xi u) a b
  -- the two defects agree
  have hdel_eq : ∀ a : ↥A, delu a = delv a := by
    intro a
    have hδ : u⁻¹ * (a : P) * u ∈ A := by
      simpa [inv_inv] using hAn.conj_mem (a : P) a.2 u⁻¹
    have hcalc : (u * c)⁻¹ * (a : P) * (u * c) * (a : P)⁻¹
        = u⁻¹ * (a : P) * u * (a : P)⁻¹ := by
      calc (u * c)⁻¹ * (a : P) * (u * c) * (a : P)⁻¹
          = c⁻¹ * ((u⁻¹ * (a : P) * u) * c) * (a : P)⁻¹ := by rw [mul_inv_rev]; group
        _ = c⁻¹ * (c * (u⁻¹ * (a : P) * u)) * (a : P)⁻¹ := by
              rw [hAb _ hδ c hcA]
        _ = u⁻¹ * (a : P) * u * (a : P)⁻¹ := by group
    refine Subtype.ext ?_
    rw [delu_coe, delv_coe, hxiu]
    exact hcalc.symm
  -- the quadratic maps `φ(a) = a² δ(a)`
  let phiu : ↥A → ↥A := fun a => a * a * delu a
  let phiv : ↥A → ↥A := fun a => a * a * delv a
  have phiu_coe : ∀ a : ↥A,
      ((phiu a : ↥A) : P) = (a : P) * (a : P) * ((delu a : ↥A) : P) := fun a => rfl
  have phiu_mul : ∀ a b : ↥A, phiu (a * b) = phiu a * phiu b := by
    intro a b
    have h1 : ((a * b) * (a * b) : ↥A) = (a * a) * (b * b) := by
      rw [← pow_two, ← pow_two, ← pow_two, mul_pow]
    show (a * b) * (a * b) * delu (a * b) = (a * a * delu a) * (b * b * delu b)
    rw [h1, delu_mul]
    ac_rfl
  have phiv_mul : ∀ a b : ↥A, phiv (a * b) = phiv a * phiv b := by
    intro a b
    have h1 : ((a * b) * (a * b) : ↥A) = (a * a) * (b * b) := by
      rw [← pow_two, ← pow_two, ← pow_two, mul_pow]
    show (a * b) * (a * b) * delv (a * b) = (a * a * delv a) * (b * b * delv b)
    rw [h1, delv_mul]
    ac_rfl
  have hphi_eq : ∀ a : ↥A, phiu a = phiv a := by
    intro a
    show a * a * delu a = a * a * delv a
    rw [hdel_eq a]
  let φu : ↥A →* ↥A := MonoidHom.mk' phiu phiu_mul
  let φv : ↥A →* ↥A := MonoidHom.mk' phiv phiv_mul
  let K : Subgroup P := (φu.range).map A.subtype
  have hKle : K ≤ A := by
    intro x hx
    obtain ⟨y, -, hyx⟩ := hx
    rw [← hyx]; exact y.2
  have hKmem : ∀ k : P, k ∈ K ↔ ∃ a : ↥A, ((phiu a : ↥A) : P) = k := by
    intro k
    constructor
    · rintro ⟨y, hy, hyk⟩
      obtain ⟨a, ha⟩ := hy
      exact ⟨a, by rw [← hyk, ← ha]; rfl⟩
    · rintro ⟨a, ha⟩
      exact ⟨(phiu a : ↥A), ⟨a, rfl⟩, ha⟩
  have hKmemv : ∀ k : P, k ∈ K ↔ ∃ a : ↥A, ((phiv a : ↥A) : P) = k := by
    intro k
    constructor
    · rintro hk
      obtain ⟨a, ha⟩ := (hKmem k).mp hk
      exact ⟨a, by rw [← ha, hphi_eq a]⟩
    · rintro ⟨a, ha⟩
      exact (hKmem k).mpr ⟨a, by rw [← ha, hphi_eq a]⟩
  -- the `ξ`-action on `φ`
  have hxi_phi : ∀ a : ↥A, xA (phiu a) = phiv (xA a) := by
    intro a
    have h1 : xA (delu a) = delv (xA a) := by
      refine Subtype.ext ?_
      simp only [xA_coe, delu_coe, delv_coe]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have h2 : xA (a * a) = xA a * xA a := by rw [map_mul]
    show xA (a * a * delu a) = (xA a) * (xA a) * delv (xA a)
    rw [map_mul, h2, h1]
  -- `ξ` fixes `K`
  have hkey1 : ∀ a : ↥A, h.xi ((phiu a : ↥A) : P) = ((phiv (xA a) : ↥A) : P) := by
    intro a
    rw [← xA_coe (phiu a), hxi_phi a]
  have hkey2 : ∀ a : ↥A, (h.xi : MulAut P).symm ((phiv a : ↥A) : P)
      = ((phiu (xA.symm a) : ↥A) : P) := by
    intro a
    have h1 : xA (phiu (xA.symm a)) = phiv a := by
      rw [hxi_phi (xA.symm a), MulEquiv.apply_symm_apply]
    have h2 : h.xi ((phiu (xA.symm a) : ↥A) : P) = ((phiv a : ↥A) : P) := by
      rw [← xA_coe (phiu (xA.symm a)), h1]
    rw [← h2]
    simp
  have hxiK : K.map (h.xi : MulAut P).toMonoidHom = K := by
    apply le_antisymm
    · rintro x ⟨k, hk, rfl⟩
      obtain ⟨a, ha⟩ := (hKmem k).mp hk
      rw [← ha]
      change h.xi ((phiu a : ↥A) : P) ∈ K
      rw [hkey1 a]
      exact (hKmemv _).mpr ⟨xA a, rfl⟩
    · intro x hx
      obtain ⟨a, ha⟩ := (hKmemv x).mp hx
      refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
      rw [← ha]
      change (h.xi : MulAut P).symm ((phiv a : ↥A) : P) ∈ K
      rw [hkey2 a]
      exact (hKmem _).mpr ⟨xA.symm a, rfl⟩
  -- `(u a)² = u² φ_u(a)`
  have hsq_formula : ∀ a : ↥A,
      (u * (a : P)) * (u * (a : P)) = (u * u) * ((phiu a : ↥A) : P) := by
    intro a
    have hδ : u⁻¹ * (a : P) * u ∈ A := by
      simpa [inv_inv] using hAn.conj_mem (a : P) a.2 u⁻¹
    have hstep1 : (a : P) * (u⁻¹ * (a : P) * u * (a : P)⁻¹) = u⁻¹ * (a : P) * u := by
      rw [show (a : P) * (u⁻¹ * (a : P) * u * (a : P)⁻¹)
            = (a : P) * (u⁻¹ * (a : P) * u) * (a : P)⁻¹ from by group,
          hAb (a : P) a.2 (u⁻¹ * (a : P) * u) hδ]
      group
    have hstep : (a : P) * (u⁻¹ * (a : P) * u)
        = (a : P) * (a : P) * (u⁻¹ * (a : P) * u * (a : P)⁻¹) := by
      rw [show (a : P) * (a : P) * (u⁻¹ * (a : P) * u * (a : P)⁻¹)
            = (a : P) * ((a : P) * (u⁻¹ * (a : P) * u * (a : P)⁻¹)) from by group,
          hstep1]
    rw [phiu_coe, delu_coe]
    calc (u * (a : P)) * (u * (a : P))
        = (u * u) * ((u⁻¹ * (a : P) * u) * (a : P)) := by group
      _ = (u * u) * ((a : P) * (u⁻¹ * (a : P) * u)) := by rw [hAb _ hδ (a : P) a.2]
      _ = (u * u) * ((a : P) * (a : P) * (u⁻¹ * (a : P) * u * (a : P)⁻¹)) := by rw [hstep]
  -- `u² ≠ 1`
  have hu2ne : u * u ≠ 1 := fun h1 =>
    huA (hOm (h.mem_omega1.mpr (by rw [pow_two]; exact h1)))
  -- the subgroup `B` generated by the squares of elements of the coset `uA`
  let B : Subgroup P :=
    Subgroup.closure {x : P | ∃ a : ↥A, (u * (a : P)) * (u * (a : P)) = x}
  have hB_gen : ∀ a : ↥A, (u * (a : P)) * (u * (a : P)) ∈ B := fun a =>
    Subgroup.subset_closure ⟨a, rfl⟩
  have hu2B : u * u ∈ B := by simpa using hB_gen 1
  have hBle : B ≤ A := by
    rw [show B = Subgroup.closure {x : P | ∃ a : ↥A, (u * (a : P)) * (u * (a : P)) = x}
      from rfl, Subgroup.closure_le]
    rintro x ⟨a, rfl⟩
    have hka : ((phiu a : ↥A) : P) ∈ A := (phiu a).2
    rw [hsq_formula a]
    exact A.mul_mem hu2A hka
  have hKleB : K ≤ B := by
    intro k hk
    obtain ⟨a, ha⟩ := (hKmem k).mp hk
    have h1 : (u * (a : P)) * (u * (a : P)) ∈ B := hB_gen a
    have h3 : ((phiu a : ↥A) : P) = (u * u)⁻¹ * ((u * (a : P)) * (u * (a : P))) := by
      rw [hsq_formula a]; group
    rw [← ha, h3]
    exact Subgroup.mul_mem B (Subgroup.inv_mem B hu2B) h1
  -- the effect of `ξ` on the generators of `B`
  have hswap : ∀ a : ↥A, h.xi ((u * (a : P)) * (u * (a : P)))
      = (u * (h.xi (a : P) * c)) * (u * (h.xi (a : P) * c)) := by
    intro a
    have h3 : h.xi (a : P) ∈ A := by
      have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
      rwa [hA.map_eq] at hm
    have hstep : h.xi u * h.xi (a : P) = u * (h.xi (a : P) * c) := by
      rw [hxiu]
      calc u * c * h.xi (a : P) = u * (c * h.xi (a : P)) := by group
        _ = u * (h.xi (a : P) * c) := by rw [hAb c hcA (h.xi (a : P)) h3]
    rw [map_mul, map_mul, hstep]
  -- `ξ` preserves `B`
  have hxiB : B.map (h.xi : MulAut P).toMonoidHom = B := by
    have hsub : B.map (h.xi : MulAut P).toMonoidHom ≤ B := by
      rw [show B = Subgroup.closure {x : P | ∃ a : ↥A, (u * (a : P)) * (u * (a : P)) = x}
        from rfl, MonoidHom.map_closure, Subgroup.closure_le]
      rintro x ⟨y, ⟨a, rfl⟩, rfl⟩
      change h.xi ((u * (a : P)) * (u * (a : P))) ∈ B
      rw [hswap a]
      exact hB_gen ⟨h.xi (a : P) * c, A.mul_mem (by
        have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
        rwa [hA.map_eq] at hm) hcA⟩
    have hsub' : B.map ((h.xi : MulAut P).symm).toMonoidHom ≤ B := by
      rw [show B = Subgroup.closure {x : P | ∃ a : ↥A, (u * (a : P)) * (u * (a : P)) = x}
        from rfl, MonoidHom.map_closure, Subgroup.closure_le]
      rintro x ⟨y, ⟨a, rfl⟩, rfl⟩
      have hrev : u = (h.xi : MulAut P).symm u * (h.xi : MulAut P).symm c := by
        have h2 := congrArg (fun t : P => (h.xi : MulAut P).symm t) hxiu
        simpa [map_mul] using h2
      have hcinv : (h.xi : MulAut P).symm u = u * ((h.xi : MulAut P).symm c)⁻¹ := by
        conv_rhs => rw [hrev]
        group
      have hcm : ((h.xi : MulAut P).symm c)⁻¹ ∈ A :=
        A.inv_mem (symm_mem_of_map_eq h.xi hA.map_eq hcA)
      have ham : (h.xi : MulAut P).symm (a : P) ∈ A :=
        symm_mem_of_map_eq h.xi hA.map_eq a.2
      have hfirst : (h.xi : MulAut P).symm (u * (a : P))
          = u * (((h.xi : MulAut P).symm c)⁻¹ * (h.xi : MulAut P).symm (a : P)) := by
        rw [map_mul, hcinv]
        group
      have h1 : (h.xi : MulAut P).symm ((u * (a : P)) * (u * (a : P)))
          = (u * (((h.xi : MulAut P).symm c)⁻¹ * (h.xi : MulAut P).symm (a : P)))
            * (u * (((h.xi : MulAut P).symm c)⁻¹ * (h.xi : MulAut P).symm (a : P))) := by
        rw [map_mul, hfirst]
      change (h.xi : MulAut P).symm ((u * (a : P)) * (u * (a : P))) ∈ B
      rw [h1]
      exact hB_gen ⟨_, A.mul_mem hcm ham⟩
    apply le_antisymm hsub
    intro x hx
    have h1 : (h.xi : MulAut P).symm x ∈ B.map ((h.xi : MulAut P).symm).toMonoidHom :=
      ⟨x, hx, rfl⟩
    exact ⟨(h.xi : MulAut P).symm x, hsub' h1, by simp⟩
  have hB_gen_mem : ∀ b ∈ ({x : P | ∃ a : ↥A,
      (u * (a : P)) * (u * (a : P)) = x} : Set P), b ∈ B :=
    fun b hb => Subgroup.subset_closure hb
  -- `ξ` acts trivially on `B / K`
  have hBtriv : ∀ b ∈ B, h.xi b * b⁻¹ ∈ K := by
    have hgen : ∀ a : ↥A, h.xi ((u * (a : P)) * (u * (a : P)))
        * ((u * (a : P)) * (u * (a : P)))⁻¹ ∈ K := by
      intro a
      have h3 : h.xi (a : P) ∈ A := by
        have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
        rwa [hA.map_eq] at hm
      have hbA : h.xi (a : P) * c ∈ A := A.mul_mem h3 hcA
      have hm1 : ((phiu ⟨h.xi (a : P) * c, hbA⟩ : ↥A) : P) ∈ A :=
        (phiu ⟨h.xi (a : P) * c, hbA⟩).2
      have hm2 : ((phiu a : ↥A) : P) ∈ A := (phiu a).2
      rw [hswap a, hsq_formula a, hsq_formula ⟨h.xi (a : P) * c, hbA⟩]
      have hX : ((phiu ⟨h.xi (a : P) * c, hbA⟩ : ↥A) : P)
          * ((phiu a : ↥A) : P)⁻¹ ∈ A := A.mul_mem hm1 (A.inv_mem hm2)
      rw [show (u * u) * ((phiu ⟨h.xi (a : P) * c, hbA⟩ : ↥A) : P)
            * (((u * u) * ((phiu a : ↥A) : P)))⁻¹
          = (u * u) * (((phiu ⟨h.xi (a : P) * c, hbA⟩ : ↥A) : P)
            * ((phiu a : ↥A) : P)⁻¹) * (u * u)⁻¹ from by group,
        mul_conj_cancel (hAb (u * u) hu2A _ hX)]
      exact K.mul_mem ((hKmem _).mpr ⟨_, rfl⟩) (K.inv_mem ((hKmem _).mpr ⟨a, rfl⟩))
    let T : Subgroup P :=
      { carrier := {y : P | y ∈ A ∧ h.xi y * y⁻¹ ∈ K}
        one_mem' := ⟨A.one_mem, by simp⟩
        mul_mem' := by
          rintro y z ⟨hyA, hyK⟩ ⟨hzA, hzK⟩
          refine ⟨A.mul_mem hyA hzA, ?_⟩
          have hxiz : h.xi z ∈ A := by
            have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hzA
            rwa [hA.map_eq] at hm
          have hconj : y * (h.xi z * z⁻¹) * y⁻¹ = h.xi z * z⁻¹ := by
            rw [hAb y hyA (h.xi z * z⁻¹) (A.mul_mem hxiz (A.inv_mem hzA))]
            group
          have hstep : h.xi (y * z) * (y * z)⁻¹
              = (h.xi y * y⁻¹) * (y * (h.xi z * z⁻¹) * y⁻¹) := by
            rw [map_mul, mul_inv_rev]; group
          rw [hstep, hconj]
          exact K.mul_mem hyK hzK
        inv_mem' := by
          rintro y ⟨hyA, hyK⟩
          refine ⟨A.inv_mem hyA, ?_⟩
          have hxiy : h.xi y ∈ A := by
            have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hyA
            rwa [hA.map_eq] at hm
          have hstep : h.xi y⁻¹ * (y⁻¹)⁻¹ = (h.xi y * y⁻¹)⁻¹ := by
            simp only [map_inv, inv_inv, mul_inv_rev]
            exact hAb _ (A.inv_mem hxiy) _ hyA
          rw [hstep]
          exact K.inv_mem hyK }
    have hBT : B ≤ T := by
      rw [show B = Subgroup.closure {x : P | ∃ a : ↥A, (u * (a : P)) * (u * (a : P)) = x}
        from rfl, Subgroup.closure_le]
      rintro x ⟨a, rfl⟩
      have hka : ((phiu a : ↥A) : P) ∈ A := (phiu a).2
      have hxA : (u * (a : P)) * (u * (a : P)) ∈ A := by
        rw [hsq_formula a]; exact A.mul_mem hu2A hka
      exact ⟨hxA, hgen a⟩
    intro b hb
    exact (hBT hb).2
  -- `B = A ^ (2 ^ s)`, `K = A ^ (2 ^ t)`
  obtain ⟨s, hsle, hs⟩ := D.hstruct B hBle hxiB
  obtain ⟨t, htle, ht⟩ := D.hstruct K hKle hxiK
  have hBne : B ≠ ⊥ := fun hbot => hu2ne (Subgroup.mem_bot.mp (hbot ▸ hu2B))
  have hslt : s < D.e := by
    by_contra hcon
    push_neg at hcon
    exact hBne (by rw [hs, powSub_eq_bot_of_exp hA.abelian hcon D.hexp])
  have hq2 : 2 ≤ qcard A := by
    have h1 : A ⊓ omega1 P = omega1 P := inf_eq_right.mpr hOm
    have h2 : qcard A = Nat.card ↥(omega1 P) :=
      congrArg (fun S : Subgroup P => Nat.card ↥S) h1
    rw [h2]
    have h3 := h.omega1_card_ge_four
    omega
  have hq1 : 1 < qcard A := by omega
  have hstle : s ≤ t := by
    by_contra hcon
    have hcon' : t < s := not_le.mp hcon
    have h1 : powSub A (2 ^ t) ≤ powSub A (2 ^ s) := by rw [← ht, ← hs]; exact hKleB
    have h2 : Nat.card ↥(powSub A (2 ^ t)) ≤ Nat.card ↥(powSub A (2 ^ s)) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h1)
    rw [D.hcard t htle, D.hcard s hsle] at h2
    have h3 : D.e - t ≤ D.e - s := (Nat.pow_le_pow_iff_right hq1).mp h2
    omega
  -- case analysis
  by_cases hcase : u * u ∈ K
  · -- `u² ∈ K`: `(u a)² = 1` for a suitable `a`, so `u a ∈ Ω₁ ≤ A`
    obtain ⟨a, ha⟩ := (hKmem _).mp (K.inv_mem hcase)
    have h1 : (u * (a : P)) * (u * (a : P)) = 1 := by
      rw [hsq_formula a, ha, mul_inv_cancel]
    have h2 : u * (a : P) ∈ omega1 P := h.mem_omega1.mpr (by rw [pow_two]; exact h1)
    refine huA ?_
    have h3 : u * (a : P) ∈ A := hOm h2
    have h5 : u = (u * (a : P)) * (a : P)⁻¹ := by group
    rw [h5]
    exact A.mul_mem h3 (A.inv_mem a.2)
  · -- `u² ∉ K`: an element of `Ω₁` fixed by `ξ`, contradicting transitivity
    have hst : s < t := by
      rcases lt_or_eq_of_le hstle with hlt | heq
      · exact hlt
      · exfalso
        apply hcase
        have h1 : powSub A (2 ^ s) = K := by rw [heq, ht]
        have h2 : u * u ∈ powSub A (2 ^ s) := by rw [← hs]; exact hu2B
        exact h1 ▸ h2
    have htpos : 1 ≤ t := by omega
    set x : P := a0 ^ 2 ^ (t - 1) with hxdef
    have hxB : x ∈ B := by
      rw [hs]
      exact powSub_le_of_dvd hA.abelian (Nat.pow_dvd_pow 2 (by omega)) (pow_mem_powSub ha0A)
    set y : P := a0 ^ 2 ^ (D.e - 1) with hydef
    have hyx : y = x ^ 2 ^ (D.e - t) := by
      rw [hydef, hxdef, ← pow_mul]
      congr 1
      rw [← pow_add]
      congr 1
      omega
    have hy2 : y * y = 1 := by
      rw [hydef, ← pow_two, ← pow_mul,
        show 2 ^ (D.e - 1) * 2 = 2 ^ D.e from by rw [← pow_succ]; congr 1; omega]
      exact D.hexp a0 ha0A
    have hyne : y ≠ 1 := by
      intro h1
      have h2 : a0 ^ 2 ^ (D.e - 1) = 1 := by rw [← hydef]; exact h1
      have h3 : orderOf a0 ∣ 2 ^ (D.e - 1) := orderOf_dvd_iff_pow_eq_one.mpr h2
      rw [ha0ord] at h3
      have h4 : 2 ^ (D.e - 1) < 2 ^ D.e := Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact absurd (Nat.le_of_dvd (pow_pos (by norm_num) _) h3) (not_le_of_gt h4)
    have hyB : y ∈ B := by
      have h1 : y ∈ powSub A (2 ^ (D.e - 1)) := by rw [hydef]; exact pow_mem_powSub ha0A
      rw [hs]
      exact powSub_le_of_dvd hA.abelian (Nat.pow_dvd_pow 2 (by omega)) h1
    -- `ξ y = y`
    have hfix : h.xi y = y := by
      have hk : h.xi x * x⁻¹ ∈ K := hBtriv x hxB
      have hk' : h.xi x * x⁻¹ ∈ powSub A (2 ^ t) := by rw [← ht]; exact hk
      obtain ⟨z, hzA, hz⟩ := (mem_powSub_iff hA.abelian).mp hk'
      have hkpow : (h.xi x * x⁻¹) ^ 2 ^ (D.e - t) = 1 := by
        rw [← hz, ← pow_mul,
          show 2 ^ t * 2 ^ (D.e - t) = 2 ^ D.e from by rw [← pow_add]; congr 1; omega,
          D.hexp z hzA]
      have hxix : h.xi x ∈ A := by
        have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom (hBle hxB)
        rwa [hA.map_eq] at hm
      have h1 : h.xi x = x * (h.xi x * x⁻¹) := by
        rw [← mul_assoc, hAb x (hBle hxB) (h.xi x) hxix]
        group
      rw [hyx, map_pow, h1]
      have hcomm : Commute x (h.xi x * x⁻¹) := hAb x (hBle hxB) _ (hKle hk)
      rw [hcomm.mul_pow, hkpow, mul_one]
    -- contradict transitivity of `ξ` on the involutions
    obtain ⟨z₁, z₂, hz1, hz2, hz12⟩ := h.manyInvol
    have hzy : orderOf y = 2 := by
      have hd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hy2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hyne
      · exact h2
    have hfixk : ∀ k : ℕ, (h.xi ^ k) y = y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hfix]
    obtain ⟨k, hk⟩ := h.trans y z₁ hzy hz1
    obtain ⟨l, hl⟩ := h.trans y z₂ hzy hz2
    exact hz12 (by rw [← hk, hfixk k, ← hl, hfixk l])

/-- **Higman 1963, Lemma 3.**  If `A` is a normal abelian `ξ`-subgroup of a Suzuki 2-group and
`C > A` is a normal `ξ`-subgroup covering `A` with `Φ(C) = A²`, then `A` has exponent at most
`4`. -/
theorem higman_lemma3_general (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : powSub C 2 ⊔ ⁅C, C⁆ = powSub A 2) :
    ∀ a ∈ A, a ^ 4 = 1 := by
  classical
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  rcases eq_or_ne A ⊥ with hbot | hAne
  · subst hbot
    intro a ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    simp
  have hOm : omega1 P ≤ A := omega1_le_of_isXiAbelNormal_ne_bot h hA hAne
  by_contra hcon
  push_neg at hcon
  obtain ⟨a0, ha0A, ha0ne⟩ := hcon
  obtain ⟨e, he1, he2, hkey⟩ := mem_powSub_two_iff h hA
  have he3 : 3 ≤ e := by
    by_contra hlt
    push_neg at hlt
    have hd : 2 ^ e ∣ 4 := by
      calc 2 ^ e ∣ 2 ^ 2 := Nat.pow_dvd_pow 2 (by omega)
        _ = 4 := by norm_num
    obtain ⟨t, ht⟩ := hd
    exact ha0ne (by rw [ht, pow_mul, he1 a0 ha0A, one_pow])
  have hC2 : powSub C 2 ≤ powSub A 2 := by rw [← hPhi]; exact le_sup_left
  have hC2A : powSub C 2 ≤ A := hC2.trans (powSub_le (n := 2) (by norm_num))
  -- the derivation `u ↦ ⁅·,u⁆` modulo `A⁴`
  obtain ⟨NB, hNBidem, hNBmul, hNBscalar, hNBchar⟩ :=
    derivFactor_exists hA hCn hCinv hAC hC2A he1 he2 hkey he3
  have hVexp : ∀ x : (↥A ⧸ (powSub A 2).subgroupOf A), x * x = 1 := by
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [pow_two] using pow_mem_powSub (A := A) (n := 2) a.2
  -- the kernel of the derivation is `A` (Higman's Lemma 2)
  have hker1 : ∀ u : ↥C, (∀ x : (↥A ⧸ (powSub A 2).subgroupOf A), NB u x = 1) →
      (u : P) ∈ A := by
    intro u hz
    by_contra huA
    have hdv : derivZero A (u : P) := (hNBchar u).mp hz
    have h4 : ∀ a ∈ A, ⁅(u : P)⁻¹, a⁆ ∈ powSub A 4 := by
      intro a ha
      have h1 := hdv a ha
      have h2 : (u : P)⁻¹ * ((a : P) * (u : P) * (a : P)⁻¹ * (u : P)⁻¹) * (u : P)
          ∈ powSub A 4 := by
        simpa using (powSub_four_normal hAn).conj_mem _ h1 (u : P)⁻¹
      have hid : (u : P)⁻¹ * ((a : P) * (u : P) * (a : P)⁻¹ * (u : P)⁻¹) * (u : P)
          = (u : P)⁻¹ * (a : P) * (u : P) * (a : P)⁻¹ := by group
      rw [hid] at h2
      simpa [commutatorElement_def] using h2
    exact (higman_lemma2 h hA hOm hAne (u := (u : P)⁻¹) (by
        intro hinv
        exact huA (by simpa using A.inv_mem hinv)) ⟨by
        rw [inv_pow]
        exact (powSub A 2).inv_mem (hC2 (pow_mem_powSub (A := C) (n := 2) u.2)), h4⟩)
  have hker2 : ∀ u : ↥C, (u : P) ∈ A → (∀ x : (↥A ⧸ (powSub A 2).subgroupOf A), NB u x = 1) := by
    intro u hu
    rw [hNBchar u]
    intro a ha
    have hcomm : a * (u : P) = (u : P) * a := hAb a ha (u : P) hu
    have h1 : a * (u : P) * a⁻¹ * (u : P)⁻¹ = 1 := by rw [hcomm]; group
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨u0, hu0C, hu0A⟩ : ∃ u ∈ C, u ∉ A := by
    by_contra hc
    push_neg at hc
    exact hCA (le_antisymm hAC (fun x hx => hc x hx))
  have hid0 : NB ⟨u0, hu0C⟩ = MonoidHom.id _ := by
    rcases hNBscalar ⟨u0, hu0C⟩ with hc | hc
    · exact absurd (hker1 ⟨u0, hu0C⟩ hc) hu0A
    · exact hc
  have hdich : ∀ u ∈ C, ∀ v ∈ C, u ∉ A → v ∉ A → u * v ∈ A := by
    intro u huC v hvC huA hvA
    have hu' : NB ⟨u, huC⟩ = MonoidHom.id _ := by
      rcases hNBscalar ⟨u, huC⟩ with hc | hc
      · exact absurd (hker1 ⟨u, huC⟩ hc) huA
      · exact hc
    have hv' : NB ⟨v, hvC⟩ = MonoidHom.id _ := by
      rcases hNBscalar ⟨v, hvC⟩ with hc | hc
      · exact absurd (hker1 ⟨v, hvC⟩ hc) hvA
      · exact hc
    have hone : ∀ x, (NB ⟨u * v, C.mul_mem huC hvC⟩) x = 1 := by
      intro x
      show (NB (⟨u, huC⟩ * ⟨v, hvC⟩ : ↥C)) x = 1
      have h1 : (NB ⟨u, huC⟩) x = x := by rw [hu']; rfl
      have h2 : (NB ⟨v, hvC⟩) x = x := by rw [hv']; rfl
      rw [hNBmul ⟨u, huC⟩ ⟨v, hvC⟩ x, h1, h2]
      exact hVexp x
    exact hker1 ⟨u * v, C.mul_mem huC hvC⟩ hone
  have htriv0 : h.xi u0 * u0⁻¹ ∈ A := by
    have hu0sq : u0 * u0 ∈ A := by
      have h1 : u0 * u0 ∈ powSub C 2 := by
        rw [← pow_two]; exact pow_mem_powSub (A := C) (n := 2) hu0C
      exact powSub_le (A := A) (n := 2) (by norm_num) (hC2 h1)
    have hxC : h.xi u0 ∈ C := by
      have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hu0C
      rwa [hCinv] at hm
    have hne : h.xi u0 ∉ A := by
      intro hcon
      exact hu0A (by simpa using symm_mem_of_map_eq h.xi hA.map_eq hcon)
    have hΞ : h.xi u0 * u0 ∈ A := hdich (h.xi u0) hxC u0 hu0C hne hu0A
    rw [show u0⁻¹ = u0 * (u0 * u0)⁻¹ from by group, ← mul_assoc]
    exact A.mul_mem hΞ (A.inv_mem hu0sq)
  exact higman_lemma3_final_step_local h hA hOm hC2 hu0C hu0A htriv0

/-- **Higman 1963, Lemma 8 (weak form).**  If `A` is a normal abelian `ξ`-subgroup of a Suzuki
2-group, and `C > A` a normal `ξ`-subgroup covering `A` with `C² ≤ A` and `⁅C,C⁆ = A`, then
`A` has exponent at most `4`. -/
theorem higman_lemma8_weak (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) :
    powSub A 4 = ⊥ := by
  classical
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  rcases eq_or_ne A ⊥ with hbot | hAne
  · -- `A = ⊥`: trivial
    subst hbot
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [powSub] at hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨x, hx, hxz⟩ := hz
        refine Subgroup.mem_bot.mpr ?_
        simp only [Subgroup.mem_bot.mp hx, one_pow] at hxz
        exact hxz.symm
    | one => exact Subgroup.mem_bot.mpr rfl
    | mul a b _ _ iha ihb =>
        exact Subgroup.mem_bot.mpr (by
          rw [Subgroup.mem_bot.mp iha, Subgroup.mem_bot.mp ihb, mul_one])
    | inv a _ iha =>
        exact Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp iha, inv_one])
  have hOm : omega1 P ≤ A := omega1_le_of_isXiAbelNormal_ne_bot h hA hAne
  -- `q = |A ⊓ Ω₁| ≥ 4`
  have hq2 : 2 ≤ qcard A := by
    have h1 : A ⊓ omega1 P = omega1 P := inf_eq_right.mpr hOm
    have h2 : qcard A = Nat.card ↥(omega1 P) :=
      congrArg (fun S : Subgroup P => Nat.card ↥S) h1
    rw [h2]
    have h3 := h.omega1_card_ge_four
    omega
  by_contra h4
  -- the exponent data of `A`
  obtain ⟨D⟩ := exists_homocyclicData h hA
  have hDe : 3 ≤ D.e := by
    by_contra hlt
    push_neg at hlt
    refine h4 ?_
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hAb).mp hy
    have hd : 2 ^ D.e ∣ 4 := by
      calc 2 ^ D.e ∣ 2 ^ 2 := Nat.pow_dvd_pow 2 (by omega)
        _ = 4 := by norm_num
    obtain ⟨t, ht⟩ := hd
    refine Subgroup.mem_bot.mpr ?_
    rw [ht, pow_mul, D.hexp a ha, one_pow]
  -- `⁅A,C⁆ = A ^ (2)`
  have hACeq : ⁅A, C⁆ = powSub A 2 := by
    have h0 := commutator_powSub_A_C h hA hCn hC2 hCd 0
    simpa [powSub_one_eq] using h0
  -- the derivation `u ↦ ⁅·,u⁆` modulo `A⁴`
  obtain ⟨e, he1, he2, hkey⟩ := mem_powSub_two_iff h hA
  have he3 : 3 ≤ e := by
    by_contra hlt
    push_neg at hlt
    refine h4 ?_
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hAb).mp hy
    have hd : 2 ^ e ∣ 4 := by
      calc 2 ^ e ∣ 2 ^ 2 := Nat.pow_dvd_pow 2 (by omega)
        _ = 4 := by norm_num
    obtain ⟨t, ht⟩ := hd
    refine Subgroup.mem_bot.mpr ?_
    rw [ht, pow_mul, he1 a ha, one_pow]
  obtain ⟨Z, hZle, hAZ, hZn, hZinv, hZchar, hZcase⟩ :=
    higman9_derivation_kernel h hA hCn hCinv hAC hC2 he1 he2 hkey he3
  rcases hZcase with hZC | hidx
  · -- ## `Z = C`: every element of `C` acts trivially on `A / A⁴`, so `A² = ⁅A,C⁆ ≤ A⁴`
    have hle : ⁅A, C⁆ ≤ powSub A 4 := by
      rw [Subgroup.commutator_le]
      intro a ha u hu
      have hzu : u ∈ Z := hZC ▸ hu
      have hdv : derivZero A u := (hZchar u hu).mp hzu
      have h1 : a * u * a⁻¹ * u⁻¹ ∈ powSub A 4 := hdv a ha
      simpa [commutatorElement_def] using h1
    have hA24 : powSub A 2 ≤ powSub A 4 := hACeq ▸ hle
    have hA42 : powSub A 4 ≤ powSub A 2 := powSub_le_of_dvd hAb (by norm_num : 2 ∣ 4)
    have hA2eq : powSub A 2 = powSub A 4 := le_antisymm hA24 hA42
    -- cardinality contradiction
    have hc1 : Nat.card ↥(powSub A 2) = (qcard A) ^ (D.e - 1) := by
      have h := D.hcard 1 (by omega)
      simpa using h
    have hc2 : Nat.card ↥(powSub A 4) = (qcard A) ^ (D.e - 2) := by
      have h := D.hcard 2 (by omega)
      simpa using h
    have hcards : Nat.card ↥(powSub A 2) = Nat.card ↥(powSub A 4) := by
      conv_lhs => rw [hA2eq]
    have hpow : (qcard A) ^ (D.e - 1) = (qcard A) ^ (D.e - 2) := by
      rw [← hc1, hcards, hc2]
    have := Nat.pow_right_injective hq2 hpow
    omega
  · -- ## the index is `2`: then `Z = A` (covering), so `C/A ≅ 𝔽₂` and `A = ⁅C,C⁆ ≤ ⁅A,C⁆ = A²`
    have hZA : Z = A := by
      rcases hcover Z hZn hZinv hAZ hZle with h1 | h1
      · exact h1
      · exfalso
        have h2 : (Z.subgroupOf C).index = 1 := by
          rw [h1, Subgroup.subgroupOf_self]
          exact Subgroup.index_top
        omega
    have hidx' : (A.subgroupOf C).index = 2 := by rw [← hZA]; exact hidx
    obtain ⟨s, hs⟩ := Subgroup.index_eq_two_iff.mp hidx'
    -- every element of `C` lies in `A · ⟨s⟩`
    have hCsup : C ≤ A ⊔ Subgroup.zpowers (s : P) := by
      intro c hc
      by_cases hcA : c ∈ A
      · exact Subgroup.mem_sup_left hcA
      · have h1 : (⟨c, hc⟩ : ↥C) * s ∈ A.subgroupOf C := by
          rcases hs ⟨c, hc⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h1
          · exact absurd ((Subgroup.mem_subgroupOf).mp h1) hcA
        have h2 : c * (s : P) ∈ A := (Subgroup.mem_subgroupOf).mp h1
        have h3 : c = (c * (s : P)) * (s : P)⁻¹ := by group
        rw [h3]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2)
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers (s : P))))
    -- `⁅C,C⁆ ≤ ⁅A,C⁆ = A²`
    haveI : A.Normal := hAn
    have hCC : ⁅C, C⁆ ≤ powSub A 2 := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨a1, ha1, k1, hk1, hxy1⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := A)
          (t := Subgroup.zpowers (s : P))).mp (hCsup hx)
      obtain ⟨a2, ha2, k2, hk2, hxy2⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := A)
          (t := Subgroup.zpowers (s : P))).mp (hCsup hy)
      rw [← hxy1, ← hxy2]
      rw [commutatorElement_mul_left_eq_conj_mul a1 k1 (a2 * k2)]
      have hk1' : ⁅k1, a2 * k2⁆ ∈ powSub A 2 := by
        obtain ⟨m1, hm1⟩ := Subgroup.mem_zpowers_iff.mp hk1
        obtain ⟨m2, hm2⟩ := Subgroup.mem_zpowers_iff.mp hk2
        subst hm1
        subst hm2
        rw [commutatorElement_mul_right_eq_mul_conj ((s : P) ^ m1) a2 ((s : P) ^ m2)]
        have h1 : ⁅(s : P) ^ m1, a2⁆ ∈ powSub A 2 := by
          have hmem : ⁅(s : P) ^ m1, a2⁆ ∈ ⁅C, A⁆ :=
            Subgroup.commutator_mem_commutator (Subgroup.zpow_mem C s.2 m1) ha2
          rwa [Subgroup.commutator_comm, hACeq] at hmem
        have h2 : ⁅(s : P) ^ m1, (s : P) ^ m2⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact Commute.zpow_zpow_self (s : P) m1 m2
        have h3 : ⁅(s : P) ^ m1, a2⁆ * a2 * ⁅(s : P) ^ m1, (s : P) ^ m2⁆ * a2⁻¹
            = ⁅(s : P) ^ m1, a2⁆ := by
          rw [h2, mul_one, mul_assoc]
          group
        rw [h3]
        exact h1
      have ha1' : ⁅a1, a2 * k2⁆ ∈ powSub A 2 := by
        obtain ⟨m2, hm2⟩ := Subgroup.mem_zpowers_iff.mp hk2
        subst hm2
        rw [commutatorElement_mul_right_eq_mul_conj a1 a2 ((s : P) ^ m2)]
        have h1 : ⁅a1, a2⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hAb a1 ha1 a2 ha2)
        have h2 : ⁅a1, (s : P) ^ m2⁆ ∈ powSub A 2 := by
          have hmem : ⁅a1, (s : P) ^ m2⁆ ∈ ⁅A, C⁆ :=
            Subgroup.commutator_mem_commutator ha1 (Subgroup.zpow_mem C s.2 m2)
          rwa [hACeq] at hmem
        have hXmem : ⁅a1, (s : P) ^ m2⁆ ∈ A :=
          powSub_le (n := 2) (by norm_num) h2
        have h3 : ⁅a1, a2⁆ * a2 * ⁅a1, (s : P) ^ m2⁆ * a2⁻¹ = ⁅a1, (s : P) ^ m2⁆ := by
          rw [h1, one_mul, hAb a2 ha2 _ hXmem]
          group
        rw [h3]
        exact h2
      exact Subgroup.mul_mem _ ((powSub_normal hAn 2).conj_mem _ hk1' a1) ha1'
    -- `A = ⁅C,C⁆ ≤ A²`, whence `|A| = |A²|`
    have hAle : A ≤ powSub A 2 := hCd ▸ hCC
    have hAeq : A = powSub A 2 :=
      le_antisymm hAle (powSub_le (n := 2) (by norm_num))
    have hc0 : Nat.card ↥A = (qcard A) ^ D.e := by
      have h := D.hcard 0 (Nat.zero_le _)
      simpa [powSub_one_eq] using h
    have hc1 : Nat.card ↥(powSub A 2) = (qcard A) ^ (D.e - 1) := by
      have h := D.hcard 1 (by omega)
      simpa using h
    have hcards : Nat.card ↥A = Nat.card ↥(powSub A 2) := by
      conv_lhs => rw [hAeq]
    have hpow : (qcard A) ^ D.e = (qcard A) ^ (D.e - 1) := by
      rw [← hc0, hcards, hc1]
    have := Nat.pow_right_injective hq2 hpow
    omega

/-! ## The first part of Higman's Lemma 9: a maximal `ξ`-invariant abelian normal subgroup has
exponent dividing `4` -/

/-- **Higman 1963, Lemma 9, first part.**  A maximal `ξ`-invariant abelian normal subgroup of a
Suzuki 2-group has exponent dividing `4`.

Take a minimal `ξ`-invariant normal covering `C > A`; then `A² = Φ(A) ≤ Φ(C) ≤ A`, so
`Φ(C) ∈ {A², A}` (no `ξ`-invariant subgroup lies strictly between `A²` and `A`).  In the first
case this is Higman's Lemma 3; in the second case either `⁅C,C⁆ = A`, which is Higman's Lemma 8,
or `⁅C,C⁆ ⊆ A²`, in which Higman's Lemma 7 makes `C` abelian, contradicting the maximality of
`A`. -/
theorem powSub_four_bot_of_maximal' {A : Subgroup P} (h : IsSuzuki2Grp P)
    (hA : IsXiAbelNormal h A) (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A) :
    powSub A 4 = ⊥ := by
  classical
  have hAn : A.Normal := hA.normal
  have hAne_top : A ≠ ⊤ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hA.abelian x (htop ▸ Subgroup.mem_top x) y (htop ▸ Subgroup.mem_top y))
  obtain ⟨C, hCn, hCinv, hAC, -, hCA, hcover⟩ :=
    MSA.exists_minimal_covering h (A := A) (M := ⊤) Subgroup.normal_top
      (by rw [Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]) le_top hAne_top.symm
  have hACne : A ≠ C := hCA.symm
  have hPhi_le : powSub C 2 ⊔ ⁅C, C⁆ ≤ A :=
    MSA.phi_le_of_minimal_covering h hAn hA.map_eq hCn hCinv hAC hACne hcover
  have hA2_le : powSub A 2 ≤ powSub C 2 ⊔ ⁅C, C⁆ :=
    (powSub_mono (n := 2) hAC).trans le_sup_left
  have hPhiC_inv : (powSub C 2 ⊔ ⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom
      = powSub C 2 ⊔ ⁅C, C⁆ := by
    rw [Subgroup.map_sup, map_powSub (h.xi : MulAut P) hCinv 2, Subgroup.map_commutator, hCinv]
  rcases xi_invariant_eq_powSub_two_or_self h hA hPhi_le hA2_le hPhiC_inv with hPhi | hPhi
  · -- `Φ(C) = A²`: Higman's Lemma 3
    have h3 := higman_lemma3_general h hA hCn hCinv hAC hACne hcover hPhi
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hA.abelian).mp hy
    simpa using h3 a ha
  · -- `Φ(C) = A`
    have hC2le : powSub C 2 ≤ A := hPhi ▸ le_sup_left
    have hCdle : ⁅C, C⁆ ≤ A := hPhi ▸ le_sup_right
    have hCdinv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨_, _, _, _, hstruct⟩ := homogeneous_structure h hA.abelian hA.map_eq
    obtain ⟨i, hCdeq⟩ := hstruct ⁅C, C⁆ hCdle hCdinv
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- `⁅C,C⁆ = A`: Higman's Lemma 8
      have hCd : ⁅C, C⁆ = A := by rw [hCdeq, hi0, pow_zero, powSub_one_eq]
      exact higman_lemma8_weak h hA hCn hCinv hAC hACne hcover hC2le hCd
    · -- `⁅C,C⁆ ⊆ A²`: Higman's Lemma 7 makes `C` abelian, against maximality
      have hCd2 : ⁅C, C⁆ ≤ powSub A 2 := by
        rw [hCdeq]
        exact powSub_le_of_dvd hA.abelian (Nat.pow_dvd_pow 2 hipos)
      have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
        higman_lemma7_general h hA hCn hCinv hAC hACne hcover hPhi hCd2
      exact absurd (hmax C ⟨hCn, hCinv, hcomm⟩ hAC) hCA


/-- **Higman 1963, Lemma 9 (existence form).**  In a Suzuki 2-group `P` there is a
`ξ`-invariant abelian normal subgroup `A`, maximal among the `ξ`-invariant abelian normal
subgroups, which contains `Ω₁(P)`, the commutator subgroup `[P,P]` and the squares of all
elements of `P` (equivalently `Φ(P) ≤ A`), and which has exponent at most `4`.

NOTE (build order): do **not** import `Submission.Work.Higman.commutator_le_omega1`; the basic
`Ω₁`-lemmas (`omega1_le_commutator`, `omega1_eq_bot_or_top_of_invariant`, ...) live in
`Submission.Work.Higman.OmegaAux`.  This statement is Higman's Lemma 9, i.e. the conjunction of
his Lemma 3, Lemma 7 and Lemma 8 over a minimal `ξ`-invariant normal cover of `A`. -/
theorem lemma9_maximal_abelian {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) :
    ∃ A : Subgroup P, A.Normal ∧ A.map (h.xi : MulAut P).toMonoidHom = A ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      (∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A) ∧
      Work.Higman.omega1 P ≤ A ∧ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A ∧ (∀ x : P, x ^ 2 ∈ A) ∧
      Work.Higman.powSub A 4 = ⊥ := by
  obtain ⟨A, hA, hmax⟩ := exists_maximal_isXiAbelNormal h
  have h4 : powSub A 4 = ⊥ := powSub_four_bot_of_maximal' h hA hmax
  have hPhi : powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A :=
    frattini_le_of_maximal h hA hmax h4
  refine ⟨A, hA.normal, hA.map_eq, hA.abelian, ?_, omega1_le_of_maximal h hA hmax, ?_, ?_, h4⟩
  · intro B hBn hBinv hBab hAB
    exact hmax B ⟨hBn, hBinv, hBab⟩ hAB
  · exact le_sup_right.trans hPhi
  · intro x
    exact hPhi ((le_sup_left : powSub (⊤ : Subgroup P) 2 ≤
      powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆)
      (pow_mem_powSub (n := 2) (Subgroup.mem_top x)))

end Work.Higman
