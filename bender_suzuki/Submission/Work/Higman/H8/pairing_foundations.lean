import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.clo_betaV_aux
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.Fq_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Foundations for the pairings of the hard case of Higman's Lemma 8

This file packages the three "representative-formula" facts that every property of the pairings
`cloBPair : C/A × C/A → Ω₁(P)` and `cloBetaV : C/A × Ω₁(P) → Ω₁(P)` rests on, together with the
elementary group-theoretic and power-subgroup calculus used by their proofs.

* `cloBPair_mk` — the commutator pairing evaluated on arbitrary representatives;
* `cloBetaV_mk` — the bracket pairing evaluated on an arbitrary representative and an arbitrary
  lift of the second argument;
* `powSub_two_ne_powSub_four` — `A² ≠ A⁴`, the source of the non-triviality of both pairings.

Everything is stated elementwise (`↑(cloBPair S x y) = ⋯`) so that no extra quotient is needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.H8

open Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Elementary commutator identities -/

/-- `⁅x*y, z⁆ = (x ⁅y,z⁆ x⁻¹) * ⁅x,z⁆`.

NB: named `..._general` to avoid a clash with `Work.Higman.commutator_mul_left` in
`OmegaAux.lean` (the class-two form `⁅x*y,z⁆ = ⁅x,z⁆*⁅y,z⁆`); the two names must stay distinct
or the import order decides which one `H8/alt_pairing_false.lean` sees. -/
theorem commutator_mul_left_general {G : Type} [Group G] (x y z : G) :
    ⁅x*y, z⁆ = (x * ⁅y,z⁆ * x⁻¹) * ⁅x,z⁆ := by
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group

/-- `⁅x, y*z⁆ = ⁅x,y⁆ * (y ⁅x,z⁆ y⁻¹)`.  (Renamed, see `commutator_mul_left_general`.) -/
theorem commutator_mul_right_general {G : Type} [Group G] (x y z : G) :
    ⁅x, y*z⁆ = ⁅x,y⁆ * (y * ⁅x,z⁆ * y⁻¹) := by
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group

/-- `⁅(r*a)⁻¹, v⁆ = ⁅r⁻¹,v⁆ * ⁅a⁻¹,v⁆` when `a` and `⁅r⁻¹,v⁆` lie in an abelian subgroup. -/
theorem commutator_inv_mul_left {G : Type} [Group G] {A : Subgroup G}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x*y = y*x) {r a v : G}
    (ha : a ∈ A) (hc : ⁅r⁻¹, v⁆ ∈ A) :
    ⁅(r * a)⁻¹, v⁆ = ⁅r⁻¹, v⁆ * ⁅a⁻¹, v⁆ := by
  have hca : a⁻¹ * ⁅r⁻¹, v⁆ = ⁅r⁻¹, v⁆ * a⁻¹ := hAb a⁻¹ (A.inv_mem ha) ⁅r⁻¹, v⁆ hc
  have hrvr : r⁻¹ * v * r = ⁅r⁻¹, v⁆ * v := by
    rw [commutatorElement_def]; group
  have e1 : ⁅(r * a)⁻¹, v⁆ = a⁻¹ * (r⁻¹ * v * r) * a * v⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e1, hrvr]
  have key : a⁻¹ * (⁅r⁻¹, v⁆ * v) * a * v⁻¹ = ⁅r⁻¹, v⁆ * (a⁻¹ * v * a * v⁻¹) := by
    rw [show a⁻¹ * (⁅r⁻¹, v⁆ * v) * a * v⁻¹ = (a⁻¹ * ⁅r⁻¹, v⁆) * (v * a * v⁻¹) from by group,
      hca]
    group
  rw [key]; simp only [commutatorElement_def, inv_inv]

/-! ## Power-subgroup calculus -/

/-- The `a⁻¹`-form of unipotence: `⁅a⁻¹, u⁆ ∈ A²` for `a ∈ A`. -/
theorem commutator_inv_mem_powSub_two {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {a u : P} (ha : a ∈ A) : ⁅a⁻¹, u⁆ ∈ powSub A 2 := by
  have hconj : u * a * u⁻¹ ∈ A := hA.normal.conj_mem a ha u
  have h1 : ⁅a⁻¹, u⁆ = ⁅u, a⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    simp only [inv_inv]
    calc a⁻¹ * u * a * u⁻¹ = a⁻¹ * (u * a * u⁻¹) := by group
      _ = (u * a * u⁻¹) * a⁻¹ := hA.abelian _ (A.inv_mem ha) _ hconj
      _ = u * a * u⁻¹ * a⁻¹ := by group
  rw [h1]
  exact commutator_mem_powSub_two h hA u a ha

/-- Powers to `2 ^ (e-1)` kill `A²`-corrections. -/
theorem mul_pow_sub_one_of_mem_two {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) {g c : P} (hg : g ∈ A)
    (hc : c ∈ powSub A 2) : (g * c) ^ 2 ^ (e - 1) = g ^ 2 ^ (e - 1) := by
  have hcA : c ∈ A := powSub_le (by norm_num) hc
  rw [Commute.mul_pow (show Commute g c from hA.abelian g hg c hcA)]
  rw [powSub_two_exp h hA he1 hc, mul_one]

/-! ## The representative formulas -/

variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

/-- **The commutator pairing on arbitrary representatives.**  For `u`, `v` representing `x`, `y`,
`↑(cloBPair S x y) = ⁅u⁻¹, v⁆ ^ 2 ^ (e-1)`. -/
theorem cloBPair_mk (S : CloH8Data h A C) (x y : ↥C ⧸ (A.subgroupOf C)) (u v : ↥C)
    (hu : QuotientGroup.mk u = x) (hv : QuotientGroup.mk v = y) :
    ((cloBPair S x y : ↥(omega1 P)) : P) = (⁅(u : P)⁻¹, (v : P)⁆) ^ 2 ^ (S.e - 1) := by
  rw [cloBPair_apply]
  set r : ↥C := cloRepC x with hr
  set s : ↥C := cloRepC y with hs
  have ha : ((r⁻¹ * u : ↥C) : P) ∈ A := cloRepC_mul_inv_mem hu
  have hb : ((s⁻¹ * v : ↥C) : P) ∈ A := cloRepC_mul_inv_mem hv
  have hru : (r : P) * ((r⁻¹ * u : ↥C) : P) = (u : P) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  have hsv : (s : P) * ((s⁻¹ * v : ↥C) : P) = (v : P) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  have hrs : ⁅(r : P)⁻¹, (s : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.inv_mem r.2) s.2
  have hfirst : (⁅(u : P)⁻¹, (v : P)⁆) ^ 2 ^ (S.e - 1) = (⁅(r : P)⁻¹, (v : P)⁆) ^ 2 ^ (S.e - 1) := by
    have hvmem : (v : P) ∈ C := v.2
    have hcv : ⁅(r : P)⁻¹, (v : P)⁆ ∈ A := by
      rw [← S.hCd]
      exact Subgroup.commutator_mem_commutator (C.inv_mem r.2) hvmem
    have hid := commutator_inv_mul_left S.hA.abelian (r := (r : P)) (a := ((r⁻¹ * u : ↥C) : P))
      (v := (v : P)) ha hcv
    rw [hru] at hid
    have ha2 : ⁅((r⁻¹ * u : ↥C) : P)⁻¹, (v : P)⁆ ∈ powSub A 2 :=
      commutator_inv_mem_powSub_two S.hA ha
    rw [hid]
    exact mul_pow_sub_one_of_mem_two S.hA S.he1 hcv ha2
  have hsecond : (⁅(r : P)⁻¹, (v : P)⁆) ^ 2 ^ (S.e - 1) = (⁅(r : P)⁻¹, (s : P)⁆) ^ 2 ^ (S.e - 1) := by
    have hcmr : ⁅(r : P)⁻¹, ((s⁻¹ * v : ↥C) : P)⁆ ∈ powSub A 2 :=
      commutator_mem_powSub_two h S.hA (r : P)⁻¹ _ hb
    have hc' : (s : P) * ⁅(r : P)⁻¹, ((s⁻¹ * v : ↥C) : P)⁆ * (s : P)⁻¹ ∈ powSub A 2 :=
      (isXiAbelNormal_powSub_two h S.hA).normal.conj_mem _ hcmr (s : P)
    have hid2 : ⁅(r : P)⁻¹, (v : P)⁆
        = ⁅(r : P)⁻¹, (s : P)⁆ * ((s : P) * ⁅(r : P)⁻¹, ((s⁻¹ * v : ↥C) : P)⁆ * (s : P)⁻¹) := by
      rw [← hsv]
      exact commutator_mul_right_general _ _ _
    rw [hid2]
    exact mul_pow_sub_one_of_mem_two S.hA S.he1 hrs hc'
  exact hsecond.symm.trans hfirst.symm

/-- **The commutator pairing in "polar" form.**  For `u`, `v ∈ C`,
`↑(cloBPair S (uA) (vA)) = ⁅v, u⁆ ^ 2 ^ (e-1)`. -/
theorem cloBPair_mk_comm (S : CloH8Data h A C) (u v : ↥C) :
    ((cloBPair S (QuotientGroup.mk u) (QuotientGroup.mk v) : ↥(omega1 P)) : P)
      = (⁅(v : P), (u : P)⁆) ^ 2 ^ (S.e - 1) := by
  rw [cloBPair_mk S _ _ u v rfl rfl]
  have hconj : ⁅(u : P)⁻¹, (v : P)⁆ = (u : P)⁻¹ * ⁅(v : P), (u : P)⁆ * (u : P) := by
    rw [commutatorElement_def, commutatorElement_def]; group
  rw [hconj]
  have hg : ⁅(v : P), (u : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator v.2 u.2
  have hgW : (⁅(v : P), (u : P)⁆) ^ 2 ^ (S.e - 1) ∈ omega1 P :=
    mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hg
  have hc : ((⁅(v : P), (u : P)⁆) ^ 2 ^ (S.e - 1)) ∈ Subgroup.center P :=
    h.omega1_le_center hgW
  have hcen := Subgroup.mem_center_iff.mp hc (u : P)
  have hconj2 : (u : P)⁻¹ * ⁅(v : P), (u : P)⁆ * (u : P)
      = (MulAut.conj (u : P)⁻¹) ⁅(v : P), (u : P)⁆ := by
    rw [MulAut.conj_apply]; simp only [inv_inv]
  rw [hconj2, ← map_pow, MulAut.conj_apply]
  simp only [inv_inv]
  rw [show (u : P)⁻¹ * ⁅(v : P), (u : P)⁆ ^ 2 ^ (S.e - 1) * (u : P)
        = (u : P)⁻¹ * (⁅(v : P), (u : P)⁆ ^ 2 ^ (S.e - 1) * (u : P)) from by group]
  rw [← hcen]
  group

/-- **The bracket pairing on arbitrary representatives and lifts.**  For `u` representing `x`,
and `a ∈ A` with `a ^ 2 ^ (e-1) = ↑w`,
`↑(cloBetaV S x w) = ⁅u, a⁆ ^ 2 ^ (e-2)`. -/
theorem cloBetaV_mk (S : CloH8Data h A C) (x : ↥C ⧸ (A.subgroupOf C)) (w : ↥(omega1 P))
    (u : ↥C) (a : ↥A) (hu : QuotientGroup.mk u = x)
    (haw : ((a : P)) ^ 2 ^ (S.e - 1) = (w : P)) :
    ((cloBetaV S x w : ↥(omega1 P)) : P) = (⁅(u : P), ((a : P))⁆) ^ 2 ^ (S.e - 2) := by
  rw [cloBetaV_apply]
  set r : ↥C := cloRepC x with hr
  set lo : ↥A := cloLiftA S w with hlo
  have hα : ((r⁻¹ * u : ↥C) : P) ∈ A := cloRepC_mul_inv_mem hu
  have hru : (r : P) * ((r⁻¹ * u : ↥C) : P) = (u : P) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  have hfirst : (⁅(u : P), ((a : P))⁆) ^ 2 ^ (S.e - 2) = (⁅(r : P), ((a : P))⁆) ^ 2 ^ (S.e - 2) := by
    have hone : ⁅((r⁻¹ * u : ↥C) : P), ((a : P))⁆ = 1 := by
      rw [commutatorElement_def]
      rw [S.hA.abelian _ hα _ a.2]
      group
    have e1 : ⁅(u : P), ((a : P))⁆ = ⁅(r : P), ((a : P))⁆ := by
      rw [← hru, commutator_mul_left_general, hone]
      group
    rw [e1]
  have hsecond : (⁅(r : P), ((lo : ↥A) : P)⁆) ^ 2 ^ (S.e - 2) = (⁅(r : P), ((a : P))⁆) ^ 2 ^ (S.e - 2) := by
    have hd : ((lo : ↥A) : P) * ((a : P))⁻¹ ∈ powSub A 2 := cloLiftA_mul_inv_mem S w a.2 haw
    have hlo_eq : ((lo : ↥A) : P) = (((lo : ↥A) : P) * ((a : P))⁻¹) * (a : P) := by group
    rw [hlo_eq, commutator_mul_right_general]
    have hdA : ((lo : ↥A) : P) * ((a : P))⁻¹ ∈ A := powSub_le (by norm_num) hd
    have hra2 : ⁅(r : P), (a : P)⁆ ∈ powSub A 2 := commutator_mem_powSub_two h S.hA (r : P) (a : P) a.2
    have hraA : ⁅(r : P), (a : P)⁆ ∈ A := powSub_le (by norm_num) hra2
    have hconj : (((lo : ↥A) : P) * ((a : P))⁻¹) * ⁅(r : P), (a : P)⁆ * (((lo : ↥A) : P) * ((a : P))⁻¹)⁻¹
        = ⁅(r : P), (a : P)⁆ := by
      rw [S.hA.abelian _ hdA _ hraA]; group
    have hrd : ⁅(r : P), ((lo : ↥A) : P) * ((a : P))⁻¹⁆ ∈ powSub A 4 := by
      have hA2 := isXiAbelNormal_powSub_two h S.hA
      have hh := commutator_mem_powSub_two h hA2 (r : P) (((lo : ↥A) : P) * ((a : P))⁻¹) hd
      rwa [powSub_powSub S.hA.abelian, show (2:ℕ)*2 = 4 from by norm_num] at hh
    rw [hconj]
    have hcomm : Commute (⁅(r : P), ((lo : ↥A) : P) * ((a : P))⁻¹⁆) (⁅(r : P), (a : P)⁆) :=
      S.hA.abelian _ (powSub_le (by norm_num) hrd) _ hraA
    rw [hcomm.mul_pow]
    rw [powSub_four_exp h S.hA S.he1 S.he2 hrd, one_mul]
  exact hsecond.trans hfirst.symm

/-! ## `Ω₁(P) ≠ ⊥`, `A ⊄ A²`, `A² ≠ A⁴` -/

/-- `Ω₁(P)` is non-trivial. -/
theorem omega1_ne_bot (h : IsSuzuki2Grp P) : omega1 P ≠ ⊥ := by
  intro hb
  obtain ⟨x, y, hx, hy, hxy⟩ := h.manyInvol
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have hx2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hx ▸ dvd_rfl)
  have hxmem : x ∈ omega1 P := h.mem_omega1.mpr hx2
  rw [hb] at hxmem
  exact hx1 (Subgroup.mem_bot.mp hxmem)

/-- `A ⊄ A²` (the kernel of the `2 ^ (e-1)`-st power map on `A` is a proper subgroup). -/
theorem not_le_powSub_two (S : CloH8Data h A C) : ¬ (A ≤ powSub A 2) := by
  intro hle
  have hAll : ∀ x ∈ A, x ^ 2 ^ (S.e - 1) = 1 := fun x hx => (S.hkey x hx).mp (hle hx)
  have hbot : powSub A (2 ^ (S.e - 1)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [mem_powSub_iff S.hA.abelian] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hAll x hx
  have : omega1 P = ⊥ := by rw [← S.htopA, hbot]
  exact omega1_ne_bot h this

/-- **`A² ≠ A⁴`.**  If the second layer collapsed then, iterating, `A` would be elementary
abelian; but `A ≠ ⊥`.  This is the source of the non-triviality of `cloBPair` and `cloBetaV`. -/
theorem powSub_two_ne_powSub_four (S : CloH8Data h A C) : powSub A 2 ≠ powSub A 4 := by
  intro hEq
  have hle : powSub A 2 ≤ powSub A 4 := le_of_eq hEq
  have hAll : ∀ x ∈ A, x ^ 2 ^ (S.e - 1) = 1 := by
    intro x hx
    have hx2 : x ^ 2 ∈ powSub A 2 := pow_mem_powSub hx
    have hx4 : x ^ 2 ∈ powSub A 4 := hle hx2
    have hthis := powSub_four_exp h S.hA S.he1 S.he2 hx4
    have hk : 2 * 2 ^ (S.e - 2) = 2 ^ (S.e - 1) := by
      have h2 := S.he2
      rw [mul_comm, ← pow_succ]
      congr 1
      omega
    rwa [← pow_mul, hk] at hthis
  have hAle : A ≤ powSub A 2 := fun x hx => (S.hkey x hx).mpr (hAll x hx)
  have hAeq : A = powSub A 2 := le_antisymm hAle (powSub_le (by norm_num))
  have hiter : ∀ k, A = powSub A (2 ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, powSub_one_eq]
    | succ k ih =>
        rw [pow_succ, ← powSub_powSub S.hA.abelian (2 ^ k) 2, ← ih]
        exact hAeq
  have hOm : A = omega1 P := by
    rw [hiter (S.e - 1)]
    exact S.htopA
  have hbot : powSub A 2 = ⊥ := by
    rw [hOm, Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [mem_powSub_iff (fun a ha b hb => h.omega1_comm ha hb)] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h.mem_omega1.mp hx
  exact S.hAne (hAeq.trans hbot)

end Work.Higman.H8
