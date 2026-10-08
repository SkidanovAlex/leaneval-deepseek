import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.COAGT.ZpowersSqOdd
import Submission.Work.CORE4.COAGT.DihedralInvolutionGen
import Submission.Work.CORE4.COAGT.GeneratorLift

open scoped commutatorElement

namespace Work.CORE4

/-! ## Auxiliary computations

Let `Z ⊴ E` be a central subgroup, `Y ≤ E` a subgroup of odd order whose image modulo `Z`
is cyclic, `y₀ ∈ Y` a lift of a generator (`GeneratorLift`), so that every `y ∈ Y` is
`y₀ ^ j * z` with `j : ℤ`, `z ∈ Z`.

The lemmas below record the arithmetic of these decompositions. -/

/-- With every element of `Y` of the form `y₀ ^ j * z` (`z ∈ Z` central), `Y` is abelian. -/
lemma mul_comm_of_zpow_mul_central {E : Type*} [Group E] {Z Y : Subgroup E}
    (hZc : Z ≤ Subgroup.center E) {y0 : E}
    (hgen : ∀ y ∈ Y, ∃ j : ℤ, ∃ z ∈ Z, y = y0 ^ j * z) :
    ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
  intro a ha b hb
  obtain ⟨j, z, hz, rfl⟩ := hgen a ha
  obtain ⟨j', z', hz', rfl⟩ := hgen b hb
  have hcz : ∀ g : E, Commute z g :=
    fun g => ((commute_iff_eq g z).mpr (Subgroup.mem_center_iff.mp (hZc hz) g)).symm
  have hcz' : ∀ g : E, Commute z' g :=
    fun g => ((commute_iff_eq g z').mpr (Subgroup.mem_center_iff.mp (hZc hz') g)).symm
  exact (Commute.mul_left
    (Commute.mul_right (Commute.zpow_zpow (Commute.refl y0) j j') (hcz' (y0 ^ j)).symm)
    (Commute.mul_right (hcz (y0 ^ j')) (hcz z'))).eq

/-- First alternative of the dichotomy: if `q` acts on the chosen lift `y₀` by
`y₀ ↦ y₀ z` (`z ∈ Z`), then `q` multiplies every element of `Y` by a central element. -/
lemma dich_triv {E : Type*} [Group E] {Z Y : Subgroup E}
    (hZc : Z ≤ Subgroup.center E) {y0 q : E}
    (hgen : ∀ y ∈ Y, ∃ j : ℤ, ∃ z ∈ Z, y = y0 ^ j * z)
    (h : (q * y0 * q⁻¹) * y0⁻¹ ∈ Z) :
    ∀ y ∈ Y, (q * y * q⁻¹) * y⁻¹ ∈ Z := by
  intro y hy
  obtain ⟨j, z, hz, rfl⟩ := hgen y hy
  set t : E := (q * y0 * q⁻¹) * y0⁻¹ with ht
  have htZ : t ∈ Z := h
  have hcent : ∀ g : E, Commute t g :=
    fun g => ((commute_iff_eq g t).mpr (Subgroup.mem_center_iff.mp (hZc htZ) g)).symm
  have hcz : ∀ g : E, Commute z g :=
    fun g => ((commute_iff_eq g z).mpr (Subgroup.mem_center_iff.mp (hZc hz) g)).symm
  have hqy : q * y0 * q⁻¹ = t * y0 := by rw [ht]; group
  have hqz : q * z * q⁻¹ = z := by rw [← (hcz q).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hkey : q * (y0 ^ j * z) * q⁻¹ = t ^ j * (y0 ^ j * z) := by
    rw [show q * (y0 ^ j * z) * q⁻¹ = (q * y0 ^ j * q⁻¹) * (q * z * q⁻¹) by group]
    rw [hqz, ← conj_zpow, hqy, Commute.mul_zpow (hcent y0) j]
    group
  rw [hkey]
  have hfin : (t ^ j * (y0 ^ j * z)) * (y0 ^ j * z)⁻¹ = t ^ j := by group
  rw [hfin]
  exact Subgroup.zpow_mem Z htZ j

/-- Second alternative of the dichotomy: if `q` acts on the chosen lift `y₀` by
`y₀ ↦ y₀⁻¹ z` (`z ∈ Z`), then `q` inverts every element of `Y` modulo a central element. -/
lemma dich_inv {E : Type*} [Group E] {Z Y : Subgroup E}
    (hZc : Z ≤ Subgroup.center E) {y0 q : E}
    (hgen : ∀ y ∈ Y, ∃ j : ℤ, ∃ z ∈ Z, y = y0 ^ j * z)
    (h : (q * y0 * q⁻¹) * y0 ∈ Z) :
    ∀ y ∈ Y, (q * y * q⁻¹) * y ∈ Z := by
  intro y hy
  obtain ⟨j, z, hz, rfl⟩ := hgen y hy
  set t : E := (q * y0 * q⁻¹) * y0 with ht
  have htZ : t ∈ Z := h
  have hcent : ∀ g : E, Commute t g :=
    fun g => ((commute_iff_eq g t).mpr (Subgroup.mem_center_iff.mp (hZc htZ) g)).symm
  have hcz : ∀ g : E, Commute z g :=
    fun g => ((commute_iff_eq g z).mpr (Subgroup.mem_center_iff.mp (hZc hz) g)).symm
  have hqy : q * y0 * q⁻¹ = t * y0⁻¹ := by rw [ht]; group
  have hqz : q * z * q⁻¹ = z := by rw [← (hcz q).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hkey : q * (y0 ^ j * z) * q⁻¹ = t ^ j * ((y0 ^ j)⁻¹ * z) := by
    rw [show q * (y0 ^ j * z) * q⁻¹ = (q * y0 ^ j * q⁻¹) * (q * z * q⁻¹) by group]
    rw [hqz, ← conj_zpow, hqy, Commute.mul_zpow (hcent (y0⁻¹)) j, inv_zpow]
    group
  rw [hkey]
  have hsub : ((y0 ^ j)⁻¹ * z) * (y0 ^ j * z) = z * z := by
    calc ((y0 ^ j)⁻¹ * z) * (y0 ^ j * z)
        = (y0 ^ j)⁻¹ * (z * y0 ^ j) * z := by group
      _ = (y0 ^ j)⁻¹ * (y0 ^ j * z) * z := by rw [(hcz (y0 ^ j)).eq]
      _ = ((y0 ^ j)⁻¹ * y0 ^ j) * (z * z) := by group
      _ = z * z := by rw [inv_mul_cancel, one_mul]
  rw [mul_assoc, hsub]
  exact Subgroup.mul_mem Z (Subgroup.zpow_mem Z htZ j) (Subgroup.mul_mem Z hz hz)

/-- If `s` normalises `Y` and every element of `Y` is `y₀ ^ j * z`, then the commutator
`⁅s, y⁆` is a power of `⁅s, y₀⁆` (this uses that `Y` is abelian). -/
lemma comm_s_zpow {E : Type*} [Group E] {Z Y : Subgroup E}
    (hZc : Z ≤ Subgroup.center E) {y0 s : E}
    (hsN : s ∈ Subgroup.normalizer (Y : Set E)) (hy0 : y0 ∈ Y)
    (hgen : ∀ y ∈ Y, ∃ j : ℤ, ∃ z ∈ Z, y = y0 ^ j * z)
    (hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) :
    ∀ y ∈ Y, ∃ j : ℤ, ⁅s, y⁆ = ⁅s, y0⁆ ^ j := by
  intro y hy
  obtain ⟨j, z, hz, rfl⟩ := hgen y hy
  refine ⟨j, ?_⟩
  have hcz : ∀ g : E, Commute z g :=
    fun g => ((commute_iff_eq g z).mpr (Subgroup.mem_center_iff.mp (hZc hz) g)).symm
  have hsz : s * z * s⁻¹ = z := by rw [← (hcz s).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hsN' : s * y0 * s⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hsN y0).mp hy0
  have haY : ⁅s, y0⁆ ∈ Y := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem Y hsN' (Subgroup.inv_mem Y hy0)
  have hcomm : Commute ⁅s, y0⁆ y0 :=
    (commute_iff_eq _ _).mpr (hYab _ haY _ hy0)
  have hkey : s * (y0 ^ j * z) * s⁻¹ = ⁅s, y0⁆ ^ j * (y0 ^ j * z) := by
    rw [show s * (y0 ^ j * z) * s⁻¹ = (s * y0 ^ j * s⁻¹) * (s * z * s⁻¹) by group]
    rw [hsz, ← conj_zpow, show s * y0 * s⁻¹ = ⁅s, y0⁆ * y0 by rw [commutatorElement_def]; group,
        Commute.mul_zpow hcomm j]
    group
  rw [commutatorElement_def, hkey]
  group

/-- If `q` and `s` both invert `Y` modulo `Z`, then `q * s` acts trivially modulo `Z`. -/
lemma triv_mul_of_inv {E : Type*} [Group E] {Z Y : Subgroup E} (hZc : Z ≤ Subgroup.center E)
    {q s : E} (hq : ∀ y ∈ Y, (q*y*q⁻¹)*y ∈ Z) (hs : ∀ y ∈ Y, (s*y*s⁻¹)*y ∈ Z) :
    ∀ y ∈ Y, ((q*s)*y*(q*s)⁻¹)*y⁻¹ ∈ Z := by
  intro y hy
  set z1 : E := (q*y*q⁻¹)*y with h1
  set z2 : E := (s*y*s⁻¹)*y with h2
  have hz1 : z1 ∈ Z := hq y hy
  have hz2 : z2 ∈ Z := hs y hy
  have hc1 : ∀ g : E, Commute z1 g :=
    fun g => ((commute_iff_eq g z1).mpr (Subgroup.mem_center_iff.mp (hZc hz1) g)).symm
  have hc2 : ∀ g : E, Commute z2 g :=
    fun g => ((commute_iff_eq g z2).mpr (Subgroup.mem_center_iff.mp (hZc hz2) g)).symm
  have e1 : s*y*s⁻¹ = z2*y⁻¹ := by rw [h2]; group
  have e2 : q*y*q⁻¹ = z1*y⁻¹ := by rw [h1]; group
  have he : ((q*s)*y*(q*s)⁻¹)*y⁻¹ = z2*z1⁻¹ := by
    rw [show (q*s)*y*(q*s)⁻¹ = q*(s*y*s⁻¹)*q⁻¹ by group, e1]
    rw [show q*(z2*y⁻¹)*q⁻¹ = z2*(q*y⁻¹*q⁻¹) by
          rw [show q*(z2*y⁻¹)*q⁻¹ = (q*z2)*y⁻¹*q⁻¹ by group, ← (hc2 q).eq]; group]
    rw [show q*y⁻¹*q⁻¹ = (q*y*q⁻¹)⁻¹ by group, e2]
    rw [show (z1*y⁻¹)⁻¹ = y*z1⁻¹ by group]
    rw [mul_assoc]
    rw [show (y*z1⁻¹)*y⁻¹ = z1⁻¹ by rw [← ((hc1 y).inv_left).eq]; group]
  rw [he]
  exact Subgroup.mul_mem Z hz2 (Subgroup.inv_mem Z hz1)

/-- An involution inverts its own commutator with any element. -/
lemma conj_commutator_self {E : Type*} [Group E] {s y : E} (hs2 : s * s = 1) :
    s * ⁅s, y⁆ * s⁻¹ = ⁅s, y⁆⁻¹ := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
  rw [commutatorElement_def]
  rw [show s * (s*y*s⁻¹*y⁻¹) * s⁻¹ = y * s * y⁻¹ * s⁻¹ by
        rw [show s * (s*y*s⁻¹*y⁻¹) * s⁻¹ = s*s*y*s⁻¹*y⁻¹*s⁻¹ by group]
        rw [hs2, one_mul, hs_inv]]
  rw [show (s*y*s⁻¹*y⁻¹)⁻¹ = y * s * y⁻¹ * s⁻¹ by group]

/-- The elements of `E` acting on `Y` by multiplication by a central element form a subgroup. -/
def actTrivSet {E : Type*} [Group E] (Z Y : Subgroup E) (hZc : Z ≤ Subgroup.center E) :
    Subgroup E where
  carrier := {q | ∀ y ∈ Y, (q * y * q⁻¹) * y⁻¹ ∈ Z}
  mul_mem' := by
    intro a b ha hb y hy
    set u : E := (b*y*b⁻¹)*y⁻¹ with hu
    have huZ : u ∈ Z := hb y hy
    have hua : (a*y*a⁻¹)*y⁻¹ ∈ Z := ha y hy
    have hcu : ∀ g : E, Commute u g :=
      fun g => ((commute_iff_eq g u).mpr (Subgroup.mem_center_iff.mp (hZc huZ) g)).symm
    have key : (a*b)*y*(a*b)⁻¹*y⁻¹ = u * ((a*y*a⁻¹)*y⁻¹) := by
      rw [show (a*b)*y*(a*b)⁻¹*y⁻¹ = a*(b*y*b⁻¹)*a⁻¹*y⁻¹ by group]
      rw [show b*y*b⁻¹ = u*y by rw [hu]; group]
      rw [← mul_assoc a u y, ← (hcu a).eq]
      group
    rw [key]
    exact Subgroup.mul_mem Z huZ hua
  one_mem' := by intro y hy; simp
  inv_mem' := by
    intro a ha y hy
    rw [inv_inv]
    set u : E := (a*y*a⁻¹)*y⁻¹ with hu
    have huZ : u ∈ Z := ha y hy
    have hcu : ∀ g : E, Commute u g :=
      fun g => ((commute_iff_eq g u).mpr (Subgroup.mem_center_iff.mp (hZc huZ) g)).symm
    have key2 : a⁻¹*y*a = u⁻¹ * y := by
      have h1 : a*y*a⁻¹ = u*y := by rw [hu]; group
      have h3 : a⁻¹*(a*y*a⁻¹)*a = a⁻¹*(u*y)*a := by rw [h1]
      rw [show a⁻¹*(a*y*a⁻¹)*a = y by group,
          show a⁻¹*(u*y)*a = u * (a⁻¹*y*a) by
            rw [show a⁻¹*(u*y)*a = (a⁻¹*u)*(y*a) by group, (hcu a⁻¹).eq.symm]; group] at h3
      calc a⁻¹*y*a = u⁻¹ * (u * (a⁻¹*y*a)) := (inv_mul_cancel_left u _).symm
        _ = u⁻¹ * y := by rw [← h3]
    rw [key2, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.inv_mem Z huZ

lemma mem_actTrivSet {E : Type*} [Group E] {Z Y : Subgroup E} {hZc : Z ≤ Subgroup.center E}
    {q : E} : q ∈ actTrivSet Z Y hZc ↔ ∀ y ∈ Y, (q*y*q⁻¹)*y⁻¹ ∈ Z := Iff.rfl

/-- In a dihedral group, every proper subgroup misses an involution (the involutions
generate the group). -/
theorem exists_involution_notMem {Q : Type*} [Group Q] {n : ℕ} (hn : 2 ≤ n)
    (e : Q ≃* DihedralGroup n) (K : Subgroup Q) (hK : K ≠ ⊤) :
    ∃ s : Q, s ∉ K ∧ orderOf s = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  have hK' : ∀ x : Q, x ^ 2 = 1 → x ∈ K := by
    intro x hx
    by_contra hxK
    exact h ⟨x, hxK, orderOf_eq_prime hx (by rintro rfl; exact hxK (K.one_mem))⟩
  have hle : Subgroup.closure {x : Q | x ^ 2 = 1} ≤ K :=
    (Subgroup.closure_le K).mpr (fun x hx => hK' x hx)
  rw [COAGT.DihedralInvolutionGen hn e] at hle
  exact hK (top_le_iff.mp hle)

/-! ## The theorem -/

/-- Pure group theory behind Bender 1981, §4 (1)–(2) (p. 224): a `2`-group acting on an odd-order
group with all actions `± 1` modulo a central subgroup.  See `CoreOddActionGroupTheory`. -/
theorem OddDihActionInvolution (I : Work.GW2.C4Inputs) :
    ∀ {E : Type} [Group E] [Finite E]
      (Z : Subgroup E) [Z.Normal], Z ≤ Subgroup.center E →
      ∀ (Q Y : Subgroup E), Q ≤ Subgroup.normalizer (Y : Set E) →
      IsPGroup 2 Q → Odd (Nat.card Y) →
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (Q ≃* DihedralGroup n)) →
      IsCyclic (Y.map (QuotientGroup.mk' Z)) →
      (∀ q ∈ Q, ∀ y ∈ Y,
        (q * y * q⁻¹) * y⁻¹ ∈ Z ∨ (q * y * q⁻¹) * y ∈ Z) →
      ∃ s ∈ Q, orderOf s = 2 ∧ ((⁅Q, Y⁆ : Subgroup E) : Set E) = Work.GW2.invSet Y s ∧
        (Y ⊓ Subgroup.centralizer ({s} : Set E) =
          Y ⊓ Subgroup.centralizer ((Q : Subgroup E) : Set E)) ∧
        IsCyclic (⁅Q, Y⁆ : Subgroup E) := by
  intro E _ _ Z _ hZc Q Y hQN hQ2 hYodd hQdih hYcyc hact
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Step 0: the generator lift and its consequences
  obtain ⟨y0, hy0, hgen⟩ := COAGT.GeneratorLift Z Y hYcyc
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := mul_comm_of_zpow_mul_central hZc hgen
  -- ## Step 1: the dichotomy
  have hDich : ∀ q ∈ Q, (∀ y ∈ Y, (q*y*q⁻¹)*y⁻¹ ∈ Z) ∨ (∀ y ∈ Y, (q*y*q⁻¹)*y ∈ Z) := by
    intro q hq
    rcases hact q hq y0 hy0 with hh | hh
    · exact Or.inl (dich_triv hZc hgen hh)
    · exact Or.inr (dich_inv hZc hgen hh)
  -- ## Step 2: the subgroup `K₀ = {q ∈ Q | q acts trivially mod Z}` is contained in `C(Y)`
  let K0 : Subgroup E := Q ⊓ actTrivSet Z Y hZc
  have hK0mem : ∀ q, q ∈ K0 ↔ q ∈ Q ∧ ∀ y ∈ Y, (q*y*q⁻¹)*y⁻¹ ∈ Z := by
    intro q
    rw [Subgroup.mem_inf, mem_actTrivSet]
  have hcop : Nat.Coprime 2 (Nat.card Y) :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr
      (fun hdiv => (Nat.not_even_iff_odd.mpr hYodd) (even_iff_two_dvd.mpr hdiv))
  have hK0central : K0 ≤ Subgroup.centralizer (Y : Set E) := by
    have hN : K0 ≤ Subgroup.normalizer (Y : Set E) := inf_le_left.trans hQN
    have hc11 : ⁅K0, ⁅K0, Y⁆⁆ = ⁅K0, Y⁆ :=
      (I.toolkit.c11i E 2 K0 Y (IsPGroup.to_le hQ2 inf_le_left) hcop hN).1
    have hK0YZ : ⁅K0, Y⁆ ≤ Z :=
      Subgroup.commutator_le.mpr (fun q hq y hy => (hK0mem q).mp hq |>.2 y hy)
    have hZcK0 : ⁅K0, Z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by
      intro q _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_center_iff.mp (hZc hz) q).symm)
    have hbot : ⁅K0, ⁅K0, Y⁆⁆ = ⊥ := by
      have h1 : ⁅K0, ⁅K0, Y⁆⁆ ≤ ⁅K0, Z⁆ := Subgroup.commutator_mono_right hK0YZ
      rw [hZcK0] at h1
      exact le_bot_iff.mp h1
    rw [hc11] at hbot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  -- ## Step 3: the uniform argument, given an involution `s` with `∀ q ∈ Q, q ∈ K₀ ∨ q s ∈ K₀`
  have hmain : ∀ s ∈ Q, orderOf s = 2 → (∀ q ∈ Q, q ∈ K0 ∨ q * s ∈ K0) →
      (((⁅Q, Y⁆ : Subgroup E) : Set E) = Work.GW2.invSet Y s ∧
        (Y ⊓ Subgroup.centralizer ({s} : Set E) =
          Y ⊓ Subgroup.centralizer ((Q : Subgroup E) : Set E)) ∧
        IsCyclic (⁅Q, Y⁆ : Subgroup E)) := by
    intro s hsQ hsord hprop
    have hsN : s ∈ Subgroup.normalizer (Y : Set E) := hQN hsQ
    have hs2 : s * s = 1 := by rw [← pow_two, ← hsord]; exact pow_orderOf_eq_one s
    -- `[Q, Y] = ⟨⁅s, y₀⁆⟩`
    have hQYle : ⁅Q, Y⁆ ≤ Subgroup.zpowers (⁅s, y0⁆) := by
      rw [Subgroup.commutator_le]
      intro q hq y hy
      rcases hprop q hq with hqK | hqsK
      · have hqC := hK0central hqK
        rw [Subgroup.mem_centralizer_iff] at hqC
        have hyq : q * y = y * q := (hqC y hy).symm
        have h1 : ⁅q, y⁆ = 1 := by rw [commutatorElement_def, hyq]; group
        rw [h1]
        exact Subgroup.one_mem _
      · have hqsC := hK0central hqsK
        rw [Subgroup.mem_centralizer_iff] at hqsC
        have hsyms : s * y * s⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hsN y).mp hy
        have hcomm' : (q*s) * (s*y*s⁻¹) = (s*y*s⁻¹) * (q*s) := (hqsC _ hsyms).symm
        have hq_eq : q = (q*s)*s := by rw [mul_assoc, hs2, mul_one]
        have hconj : q * y * q⁻¹ = s * y * s⁻¹ := by
          rw [hq_eq, mul_inv_rev]
          rw [show ((q*s)*s)*y*(s⁻¹*(q*s)⁻¹) = (q*s)*(s*y*s⁻¹)*(q*s)⁻¹ by group]
          rw [hcomm']; group
        have h1 : ⁅q, y⁆ = ⁅s, y⁆ := by
          rw [commutatorElement_def, commutatorElement_def, hconj]
        rw [h1]
        obtain ⟨j, hj⟩ := comm_s_zpow hZc hsN hy0 hgen hYab y hy
        rw [hj]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
    have hQYge : Subgroup.zpowers (⁅s, y0⁆) ≤ ⁅Q, Y⁆ :=
      Subgroup.zpowers_le.mpr (Subgroup.commutator_mem_commutator hsQ hy0)
    have hQYeq : ⁅Q, Y⁆ = Subgroup.zpowers (⁅s, y0⁆) := le_antisymm hQYle hQYge
    -- the set identity `[Q,Y] = I_Y(s)`
    have hsinv : ∀ y ∈ Y, ⁅s, y⁆ ∈ Work.GW2.invSet Y s := by
      intro y hy
      refine ⟨?_, conj_commutator_self hs2⟩
      rw [commutatorElement_def]
      exact Subgroup.mul_mem Y ((Subgroup.mem_normalizer_iff.mp hsN y).mp hy) (Subgroup.inv_mem Y hy)
    have hset : ((⁅Q, Y⁆ : Subgroup E) : Set E) = Work.GW2.invSet Y s := by
      rw [hQYeq]
      ext x
      constructor
      · intro hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨h1Y, h1c⟩ := hsinv y0 hy0
        refine ⟨Subgroup.zpow_mem Y h1Y k, ?_⟩
        rw [← conj_zpow, h1c, inv_zpow]
      · intro hx
        obtain ⟨hxY, hxc⟩ := hx
        have hpsi : ⁅s, x⁆ = x⁻¹ * x⁻¹ := by rw [commutatorElement_def, hxc]
        obtain ⟨k, hk⟩ := comm_s_zpow hZc hsN hy0 hgen hYab x hxY
        have hodd : Odd (orderOf x⁻¹) := by
          rw [orderOf_inv]
          exact Odd.of_dvd_nat hYodd (Subgroup.orderOf_dvd_natCard Y hxY)
        have hsq : Subgroup.zpowers (x⁻¹ * x⁻¹) = Subgroup.zpowers x := by
          rw [← pow_two, COAGT.ZpowersSqOdd x⁻¹ hodd, Subgroup.zpowers_inv]
        have hmem : x⁻¹ * x⁻¹ ∈ Subgroup.zpowers (⁅s, y0⁆) := by
          rw [← hpsi, hk]
          exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
        exact (Subgroup.zpowers_le.mpr hmem) (hsq ▸ Subgroup.mem_zpowers x)
    -- the centralizer identity
    have hcen : Y ⊓ Subgroup.centralizer ({s} : Set E) =
        Y ⊓ Subgroup.centralizer ((Q : Subgroup E) : Set E) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.mp hx
        rw [Subgroup.mem_inf]
        refine ⟨hxY, ?_⟩
        rw [Subgroup.mem_centralizer_iff] at hxC ⊢
        intro q hq
        rcases hprop q hq with hqK | hqsK
        · have hqC := hK0central hqK
          rw [Subgroup.mem_centralizer_iff] at hqC
          exact (hqC x hxY).symm
        · have hqsC := hK0central hqsK
          rw [Subgroup.mem_centralizer_iff] at hqsC
          have hxs : s * x = x * s := hxC s (Set.mem_singleton s)
          have htx : (q*s) * x = x * (q*s) := (hqsC x hxY).symm
          have hq_eq : q = (q*s)*s := by rw [mul_assoc, hs2, mul_one]
          have hconj : q * x * q⁻¹ = x := by
            rw [hq_eq, mul_inv_rev]
            rw [show ((q*s)*s)*x*(s⁻¹*(q*s)⁻¹) = (q*s)*(s*x*s⁻¹)*(q*s)⁻¹ by group]
            rw [show s*x*s⁻¹ = x by rw [hxs]; group]
            rw [htx]; group
          calc q * x = q * x * q⁻¹ * q := by group
            _ = x * q := by rw [hconj]
      · intro x hx
        obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.mp hx
        rw [Subgroup.mem_inf]
        refine ⟨hxY, ?_⟩
        rw [Subgroup.mem_centralizer_iff] at hxC ⊢
        intro h hh
        have hhs : h = s := Set.mem_singleton_iff.mp hh
        rw [hhs]
        exact hxC s hsQ
    exact ⟨hset, hcen, hQYeq ▸ Subgroup.isCyclic_zpowers (⁅s, y0⁆)⟩
  -- ## Step 4: produce the involution `s`
  by_cases hK : K0 = Q
  · -- Case A: `Q` acts trivially on `Y` modulo `Z`; any involution of `Q` works
    obtain ⟨n, hn, ⟨e⟩⟩ := hQdih
    have hsord : orderOf ((e.symm (DihedralGroup.sr 0) : ↥Q) : E) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact (orderOf_injective e.symm.toMonoidHom e.symm.injective (DihedralGroup.sr 0)).trans
        (DihedralGroup.orderOf_sr 0)
    refine ⟨((e.symm (DihedralGroup.sr 0) : ↥Q) : E), (e.symm (DihedralGroup.sr 0)).2, hsord, ?_⟩
    exact hmain _ (e.symm (DihedralGroup.sr 0)).2 hsord
      (fun q hq => Or.inl (by rw [hK]; exact hq))
  · -- Case B: an involution of `Q` lying outside `K₀`
    obtain ⟨n, hn, ⟨e⟩⟩ := hQdih
    have hKq : K0.subgroupOf Q ≠ ⊤ := by
      intro h
      apply hK
      have hmap : Subgroup.map Q.subtype (K0.subgroupOf Q) = K0 :=
        Subgroup.map_subgroupOf_eq_of_le inf_le_left
      rw [h, show Subgroup.map Q.subtype (⊤ : Subgroup ↥Q) = Q by
              rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]] at hmap
      exact hmap.symm
    obtain ⟨s0, hs0K, hs0ord⟩ := exists_involution_notMem hn e (K0.subgroupOf Q) hKq
    have hsQ : (s0 : E) ∈ Q := s0.2
    have hsnotK : (s0 : E) ∉ K0 := by
      intro hsK
      exact hs0K (by rw [Subgroup.mem_subgroupOf]; exact hsK)
    have hsord : orderOf (s0 : E) = 2 := by rw [Subgroup.orderOf_coe]; exact hs0ord
    have hprop : ∀ q ∈ Q, q ∈ K0 ∨ q * (s0 : E) ∈ K0 := by
      intro q hq
      by_cases hqK : q ∈ K0
      · exact Or.inl hqK
      · refine Or.inr ((hK0mem _).mpr ⟨Q.mul_mem hq hsQ, ?_⟩)
        have hqInv : ∀ y ∈ Y, (q*y*q⁻¹)*y ∈ Z := by
          rcases hDich q hq with h | h
          · exact absurd ((hK0mem q).mpr ⟨hq, h⟩) hqK
          · exact h
        have hsInv : ∀ y ∈ Y, ((s0:E)*y*(s0:E)⁻¹)*y ∈ Z := by
          rcases hDich (s0 : E) hsQ with h | h
          · exact absurd ((hK0mem _).mpr ⟨hsQ, h⟩) hsnotK
          · exact h
        exact triv_mul_of_inv hZc hqInv hsInv
    exact ⟨(s0 : E), hsQ, hsord, hmain _ hsQ hsord hprop⟩

end Work.CORE4
