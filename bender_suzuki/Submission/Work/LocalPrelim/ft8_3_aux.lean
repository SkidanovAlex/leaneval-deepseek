import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.omega_one_eq_omega1
import Submission.Work.PGroup.omega_conj
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure
import Submission.Work.LocalPrelim.exists_invariant_index_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
open scoped Classical Pointwise commutatorElement
open Subgroup

namespace Work.LocalPrelim

variable {H : Type*} [Group H]

/-- Membership in `Ω₁(A)` for abelian `A`: an element of `A` of order dividing `p`. -/
theorem mem_omega1_iff {A : Subgroup H} (hAab : IsMulCommutative A) {p : ℕ} {z : H} :
    z ∈ Work.PGroup.omega1 H p A ↔ z ∈ A ∧ z ^ p = 1 := by
  constructor
  · intro hz
    exact Work.PGroup.omega1_mem_and_pow hAab hz
  · rintro ⟨hzA, hzp⟩
    exact Work.PGroup.omega1_subset p hzA hzp

/-- In an abelian subgroup `A`, `⁅a,y⁆^p = ⁅a^p,y⁆` for `a ∈ A` with `y` normalizing `A`. -/
theorem commutator_pow_eq_commutator_pow {A : Subgroup H} (hAab : IsMulCommutative A) {p : ℕ}
    {a y : H} (ha : a ∈ A) (hyA : y * a * y⁻¹ ∈ A) :
    (⁅a, y⁆) ^ p = ⁅a ^ p, y⁆ := by
  have hcomm : Commute a (y * a * y⁻¹) := setLike_mul_comm ha hyA
  have h1 : ⁅a, y⁆ = a * (y * a * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  have h2 : ⁅a ^ p, y⁆ = a ^ p * (y * a ^ p * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  have h3 : y * a ^ p * y⁻¹ = (y * a * y⁻¹) ^ p := by rw [conj_pow]
  rw [h1, h2, h3, hcomm.inv_right.mul_pow p, inv_pow]

/-- If `y` centralizes `Ω₁(A) ⊆ A` (abelian `A`, `y` normalizing `A`) and `a^p ∈ Ω₁(A)`,
then `⁅a,y⁆ ∈ Ω₁(A)`. -/
theorem commutator_mem_omega1_of_pow_mem {A : Subgroup H} (hAab : IsMulCommutative A) {p : ℕ}
    {a y : H} (ha : a ∈ A) (hyA : y * a * y⁻¹ ∈ A)
    (hyΩ : ∀ ω ∈ Work.PGroup.omega1 H p A, y * ω = ω * y)
    (hap : a ^ p ∈ Work.PGroup.omega1 H p A) :
    ⁅a, y⁆ ∈ Work.PGroup.omega1 H p A := by
  have hmem : ⁅a, y⁆ ∈ A := by
    have h : ⁅a, y⁆ = a * (y * a * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [h]
    exact A.mul_mem ha (A.inv_mem hyA)
  refine (mem_omega1_iff hAab).mpr ⟨hmem, ?_⟩
  rw [commutator_pow_eq_commutator_pow hAab ha hyA]
  have h1 : ⁅a ^ p, y⁆ = a ^ p * (y * a ^ p * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [h1, hyΩ (a ^ p) hap]
  group

theorem commutator_pow_right_eq {a y : H}
    (hycm : ∀ n : ℕ, y ^ n * ⁅a, y⁆ * (y ^ n)⁻¹ = ⁅a, y⁆) :
    ∀ n : ℕ, ⁅a, y ^ n⁆ = ⁅a, y⁆ ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutatorElement_mul_right_eq_mul_conj, ih]
    rw [show ⁅a, y⁆ ^ n * y ^ n * ⁅a, y⁆ * (y ^ n)⁻¹
          = ⁅a, y⁆ ^ n * (y ^ n * ⁅a, y⁆ * (y ^ n)⁻¹) from by group, hycm n]
    rw [pow_succ]

/-- The "easy case": `⁅a,z⁆ ∈ Ω` for all `a ∈ A`, `z ∈ ⟨y⟩`, when all `p`-th powers of
elements of `A` already lie in `Ω` (and `y` centralizes `Ω`). -/
theorem commutator_zpow_mem {Ω : Subgroup H} {a y : H}
    (hyΩ : ∀ ω ∈ Ω, y * ω = ω * y)
    (hcommΩ : ⁅a, y⁆ ∈ Ω) :
    ∀ j : ℤ, ⁅a, y ^ j⁆ ∈ Ω := by
  intro j
  have hcy : Commute y ⁅a, y⁆ := by
    rw [commute_iff_eq]; exact hyΩ ⁅a, y⁆ hcommΩ
  have hyd : Commute y⁻¹ ⁅a, y⁆ := hcy.inv_left
  have hycm : ∀ n : ℕ, y ^ n * ⁅a, y⁆ * (y ^ n)⁻¹ = ⁅a, y⁆ := by
    intro n
    rw [(hcy.pow_left n).eq]; group
  have hinv : ⁅a, y⁻¹⁆ = ⁅a, y⁆⁻¹ := by
    rw [commutatorElement_inv_right, ← commutatorElement_inv a y]
    rw [(hyd.inv_right).eq]; group
  have hycm' : ∀ m : ℕ, (y⁻¹) ^ m * ⁅a, y⁻¹⁆ * ((y⁻¹) ^ m)⁻¹ = ⁅a, y⁻¹⁆ := by
    intro m
    rw [hinv]
    have h2 : Commute y⁻¹ ⁅a, y⁆⁻¹ := hyd.inv_right
    rw [(h2.pow_left m).eq]; group
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg j
  · rw [hn, zpow_natCast, commutator_pow_right_eq hycm n]
    exact Ω.pow_mem hcommΩ n
  · rw [hn, zpow_neg, zpow_natCast, show (y ^ n)⁻¹ = (y⁻¹) ^ n by rw [inv_pow],
      commutator_pow_right_eq hycm' n, hinv]
    exact Ω.pow_mem (Ω.inv_mem hcommΩ) n


/-- The "easy case": `⁅A,⟨y⟩⁆ ≤ Ω₁(A)` when all `p`-th powers of elements of `A` are in `Ω₁(A)`. -/
theorem commutator_le_omega1_of_pow_mem {A : Subgroup H} (hAab : IsMulCommutative A) {p : ℕ}
    {y : H} (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hyΩ : ∀ ω ∈ Work.PGroup.omega1 H p A, y * ω = ω * y)
    (hp : ∀ a ∈ A, a ^ p ∈ Work.PGroup.omega1 H p A) :
    ⁅A, Subgroup.zpowers y⁆ ≤ Work.PGroup.omega1 H p A := by
  rw [Subgroup.commutator_le]
  intro a ha z hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact commutator_zpow_mem (Ω := Work.PGroup.omega1 H p A) hyΩ
    (commutator_mem_omega1_of_pow_mem (A := A) (a := a) (y := y) hAab ha (hyA a ha) hyΩ (hp a ha)) j

/-- If a finite subgroup `E` is normalised by `y`, it is normalised by every power of `y`. -/
theorem zpow_mem_normalizer_of_finite {E : Subgroup H} [Finite E] {y : H}
    (hinv : ∀ f ∈ E, y * f * y⁻¹ ∈ E) {j : ℤ} : y ^ j ∈ Subgroup.normalizer (E : Set H) := by
  have hsurj : ∀ f ∈ E, ∃ f' ∈ E, y * f' * y⁻¹ = f := by
    intro f hf
    let φ : E → E := fun g => ⟨y * (g : H) * y⁻¹, hinv g g.2⟩
    have hφinj : Function.Injective φ := by
      intro a b hab
      have h1 : y * (a : H) * y⁻¹ = y * (b : H) * y⁻¹ := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    obtain ⟨g, hg⟩ := Finite.surjective_of_injective hφinj ⟨f, hf⟩
    exact ⟨g.1, g.2, congrArg Subtype.val hg⟩
  have hyN : y ∈ Subgroup.normalizer (E : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf; exact hinv f hf
    · intro hf
      obtain ⟨f', hf', hff'⟩ := hsurj (y * f * y⁻¹) hf
      have hEq : f' = f := mul_left_cancel (mul_right_cancel hff')
      rw [← hEq]; exact hf'
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set H) :=
    Subgroup.zpowers_le.mpr hyN
  exact hle (Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) j)

/-- In a finite group, `y`-invariance of `E` gives invariance under every integral power, and any
element of `E ⊔ ⟨y⟩` is of the form `e * y^j`. -/
theorem mem_sup_zpowers_of_finite {E : Subgroup H} [Finite E] {y : H}
    (hinv : ∀ f ∈ E, y * f * y⁻¹ ∈ E) {z : H} (hz : z ∈ E ⊔ Subgroup.zpowers y) :
    ∃ e ∈ E, ∃ j : ℤ, e * y ^ j = z := by
  have hzinv : ∀ (j : ℤ) (f : H), f ∈ E → y ^ j * f * y ^ (-j) ∈ E := by
    intro j f hf
    have hmem : y ^ j ∈ Subgroup.normalizer (E : Set H) :=
      zpow_mem_normalizer_of_finite hinv (j := j)
    have := (Subgroup.mem_normalizer_iff.mp hmem f).mp hf
    -- `this : y^j * f * (y^j)⁻¹ ∈ E`; rewrite the inverse as `y^(-j)`
    rwa [show (y ^ j)⁻¹ = y ^ (-j) by rw [zpow_neg]] at this
  rw [Subgroup.sup_eq_closure] at hz
  have key : ∀ w ∈ Subgroup.closure ((E : Set H) ∪ (Subgroup.zpowers y : Set H)),
      ∃ e ∈ E, ∃ j : ℤ, e * y ^ j = w := by
    intro w hw
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hw
    · intro x hx
      rcases hx with hxE | hxy
      · exact ⟨x, hxE, 0, by simp⟩
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxy
        exact ⟨1, E.one_mem, j, by simp⟩
    · exact ⟨1, E.one_mem, 0, by simp⟩
    · intro a b _ _ iha ihb
      obtain ⟨e₁, he₁, j₁, rfl⟩ := iha
      obtain ⟨e₂, he₂, j₂, rfl⟩ := ihb
      refine ⟨e₁ * (y ^ j₁ * e₂ * y ^ (-j₁)), E.mul_mem he₁ (hzinv j₁ e₂ he₂), j₁ + j₂, ?_⟩
      rw [zpow_add]; group
    · intro a _ iha
      obtain ⟨e, he, j, rfl⟩ := iha
      refine ⟨y ^ (-j) * e⁻¹ * y ^ j,
        by simpa [neg_neg] using hzinv (-j) (e⁻¹) (E.inv_mem he), -j, ?_⟩
      rw [mul_inv_rev, show (y ^ j)⁻¹ = y ^ (-j) by rw [zpow_neg]]; group
  exact key z hz


/-- If `⁅c,d⁆` commutes with both `d` and `c`, then `(d*c)^n = d^n * c^n * ⁅c,d⁆^(n.choose 2)`. -/
theorem mul_pow_eq_pow_mul_pow_mul_commutator_pow {G : Type*} [Group G] {d c : G}
    (hd : Commute d ⁅c, d⁆) (hc : Commute c ⁅c, d⁆) (n : ℕ) :
    (d * c) ^ n = d ^ n * c ^ n * ⁅c, d⁆ ^ (n.choose 2) := by
  have hzd : Commute ⁅c, d⁆ d := hd.symm
  have hzc : Commute ⁅c, d⁆ c := hc.symm
  have hcd : c * d = ⁅c, d⁆ * (d * c) := by
    rw [commutatorElement_def]; group
  have key : ∀ m : ℕ, c ^ m * d = ⁅c, d⁆ ^ m * (d * c ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc c ^ (m + 1) * d = c * (c ^ m * d) := by rw [pow_succ']; group
        _ = c * (⁅c, d⁆ ^ m * (d * c ^ m)) := by rw [ih]
        _ = (c * ⁅c, d⁆ ^ m) * (d * c ^ m) := by group
        _ = (⁅c, d⁆ ^ m * c) * (d * c ^ m) := by rw [(hc.pow_right m).eq]
        _ = ⁅c, d⁆ ^ m * (c * d) * c ^ m := by group
        _ = ⁅c, d⁆ ^ m * (⁅c, d⁆ * (d * c)) * c ^ m := by rw [hcd]
        _ = ⁅c, d⁆ ^ (m + 1) * (d * c ^ (m + 1)) := by rw [pow_succ, pow_succ]; group
  have hkey : ∀ n : ℕ, (d * c) ^ n = ⁅c, d⁆ ^ (n.choose 2) * (d ^ n * c ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (d * c) ^ (n + 1) = (d * c) ^ n * (d * c) := by rw [pow_succ]
        _ = ⁅c, d⁆ ^ n.choose 2 * (d ^ n * c ^ n) * (d * c) := by rw [ih]
        _ = ⁅c, d⁆ ^ n.choose 2 * (d ^ n * (c ^ n * d)) * c := by group
        _ = ⁅c, d⁆ ^ n.choose 2 * (d ^ n * (⁅c, d⁆ ^ n * (d * c ^ n))) * c := by rw [key n]
        _ = ⁅c, d⁆ ^ n.choose 2 * ((d ^ n * ⁅c, d⁆ ^ n) * (d * c ^ (n+1))) := by group
        _ = ⁅c, d⁆ ^ n.choose 2 * ((⁅c, d⁆ ^ n * d ^ n) * (d * c ^ (n+1))) := by
              rw [((hzd.symm.pow_left n).pow_right n).eq]
        _ = (⁅c, d⁆ ^ n.choose 2 * ⁅c, d⁆ ^ n) * (d ^ (n+1) * c ^ (n+1)) := by group
        _ = ⁅c, d⁆ ^ (n.choose 2 + n) * (d ^ (n+1) * c ^ (n+1)) := by rw [← pow_add]
        _ = ⁅c, d⁆ ^ ((n+1).choose 2) * (d ^ (n+1) * c ^ (n+1)) := by
              rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
  rw [hkey n]
  rw [show ⁅c, d⁆ ^ n.choose 2 * (d ^ n * c ^ n) = (⁅c, d⁆ ^ n.choose 2 * d ^ n) * c ^ n
        from by group]
  rw [((hzd.pow_left (n.choose 2)).pow_right n).eq]
  rw [show d ^ n * ⁅c, d⁆ ^ n.choose 2 * c ^ n = d ^ n * (⁅c, d⁆ ^ n.choose 2 * c ^ n)
        from by group]
  rw [((hzc.pow_left (n.choose 2)).pow_right n).eq]
  group


/-- Conjugation by an integral power of `y` preserves a finite `y`-invariant subgroup. -/
theorem conj_zpow_mem_of_finite {E : Subgroup H} [Finite E] {y : H}
    (hinv : ∀ f ∈ E, y * f * y⁻¹ ∈ E) {e : H} (he : e ∈ E) (j : ℤ) :
    y ^ j * e * y ^ (-j) ∈ E := by
  have hmem : y ^ j ∈ Subgroup.normalizer (E : Set H) :=
    zpow_mem_normalizer_of_finite hinv (j := j)
  have h := (Subgroup.mem_normalizer_iff.mp hmem e).mp he
  rwa [show (y ^ j)⁻¹ = y ^ (-j) by rw [zpow_neg]] at h

/-- `y^j * e * y^(-j) ∈ A` when `e ∈ A` and `y` normalises `A`. -/
theorem conj_zpow_mem_of_le {A : Subgroup H} {y : H} (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    [Finite A] {e : H} (he : e ∈ A) (j : ℤ) : y ^ j * e * y ^ (-j) ∈ A :=
  conj_zpow_mem_of_finite hyA he j

/-- `(e * y^j)^p = e^p` when `y^p = 1`, `⁅y^j,e⁆ ∈ Ω`, `Ω` is `y`-central and `e ∈ A ⊇ Ω`. -/
theorem mul_zpow_pow_eq {p : ℕ} (hpodd : Odd p) {Ω A : Subgroup H} (hΩA : Ω ≤ A)
    (hΩeq : Ω = Work.PGroup.omega1 H p A) (hAab : IsMulCommutative A) {e y : H} (j : ℤ)
    (heA : e ∈ A)
    (hyΩ : ∀ ω ∈ Ω, y * ω = ω * y)
    (hcΩ : ⁅y ^ j, e⁆ ∈ Ω) (hypj : (y ^ j) ^ p = 1) :
    (e * y ^ j) ^ p = e ^ p := by
  have hcA : ⁅y ^ j, e⁆ ∈ A := hΩA hcΩ
  have hcen1 : Commute e ⁅y ^ j, e⁆ := setLike_mul_comm heA hcA
  have hcen2 : Commute (y ^ j) ⁅y ^ j, e⁆ := by
    have hcy : Commute y ⁅y ^ j, e⁆ := by
      rw [commute_iff_eq]; exact hyΩ _ hcΩ
    exact hcy.zpow_left j
  have hpow := mul_pow_eq_pow_mul_pow_mul_commutator_pow hcen1 hcen2 p
  -- `(⁅y^j,e⁆)^(p.choose 2) = 1`
  have hcΩp : ⁅y ^ j, e⁆ ^ p = 1 := by
    rw [hΩeq] at hcΩ
    exact Work.PGroup.omega1_pow_eq_one hAab hcΩ
  have hz : ⁅y ^ j, e⁆ ^ (p.choose 2) = 1 := by
    have h2 : p.choose 2 = p * ((p - 1) / 2) := by
      rw [Nat.choose_two_right]
      obtain ⟨k, hk⟩ := hpodd
      exact Nat.mul_div_assoc p ⟨k, by omega⟩
    rw [h2, pow_mul, hcΩp, one_pow]
  rw [hpow, hz, hypj, mul_one, mul_one]

/-- `Ω₁(E ⊔ ⟨y⟩) = Ω₁(A) ⊔ ⟨y⟩` when `E ≤ A` is `y`-invariant, `y` centralizes `Ω₁(A) ≤ E`,
`y^p = 1` and `⁅E,⟨y⟩⁆ ≤ Ω₁(A)`. -/
theorem omega1_sup_zpowers_eq {p : ℕ} (_hp : p.Prime) (hpodd : Odd p)
    {A E : Subgroup H} (hAab : IsMulCommutative A) (hEA : E ≤ A) [Finite A]
    {y : H} (_hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hyp : y ^ p = 1)
    (hyΩ : ∀ ω ∈ Work.PGroup.omega1 H p A, y * ω = ω * y)
    (hEinv : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hΩE : Work.PGroup.omega1 H p A ≤ E)
    (hEI : ⁅E, Subgroup.zpowers y⁆ ≤ Work.PGroup.omega1 H p A) :
    Work.PGroup.omega1 H p (E ⊔ Subgroup.zpowers y) =
      Work.PGroup.omega1 H p A ⊔ Subgroup.zpowers y := by
  set Ω := Work.PGroup.omega1 H p A with hΩ
  haveI : Finite ↥E := Finite.of_injective (Subgroup.inclusion hEA) (Subgroup.inclusion_injective hEA)
  haveI : Finite ↥Ω := Finite.of_injective (Subgroup.inclusion hΩE) (Subgroup.inclusion_injective hΩE)
  have hΩA : Ω ≤ A := Work.PGroup.omega1_le p A
  -- easy inclusion
  have h1 : Ω ⊔ Subgroup.zpowers y ≤ Work.PGroup.omega1 H p (E ⊔ Subgroup.zpowers y) := by
    rw [Work.PGroup.omega1]
    refine sup_le ?_ ?_
    · exact Subgroup.closure_mono (by
        rintro z ⟨hzA, hzp⟩
        exact ⟨Subgroup.mem_sup_left (hΩE (Work.PGroup.omega1_subset p hzA hzp)), hzp⟩)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers y), hyp⟩
  have h2 : Work.PGroup.omega1 H p (E ⊔ Subgroup.zpowers y) ≤ Ω ⊔ Subgroup.zpowers y := by
    rw [Work.PGroup.omega1, Subgroup.closure_le]
    rintro z ⟨hzB, hzp⟩
    obtain ⟨e, he, j, hje⟩ := mem_sup_zpowers_of_finite (E := E) hEinv hzB
    rw [← hje] at hzp ⊢
    have hcommΩ : ⁅y ^ j, e⁆ ∈ Ω := by
      have h := Subgroup.commutator_le.mp hEI e he (y ^ j)
        (Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) j)
      have h2 : ⁅y ^ j, e⁆ = ⁅e, y ^ j⁆⁻¹ := (commutatorElement_inv e (y ^ j)).symm
      rw [h2]
      exact Ω.inv_mem h
    have hyj : (y ^ j) ^ p = 1 := by
      have h1 : (y ^ j) ^ p = (y ^ j) ^ (p : ℤ) := by rw [zpow_natCast]
      rw [h1, ← zpow_mul, mul_comm j (p : ℤ), zpow_mul, zpow_natCast, hyp, one_zpow]
    have hep : e ^ p = 1 := by
      have := mul_zpow_pow_eq hpodd hΩA hΩ hAab j (hEA he) hyΩ hcommΩ hyj
      rw [this] at hzp
      exact hzp
    have heΩ : e ∈ Ω := by
      rw [mem_omega1_iff hAab]
      exact ⟨hEA he, hep⟩
    exact Subgroup.mul_mem (Ω ⊔ Subgroup.zpowers y) (Subgroup.mem_sup_left heΩ)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) j))
  exact le_antisymm h2 h1


/-- FT 8.3, class-two step. -/
theorem commutator_le_of_index_p {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {A E B : Subgroup H} (hAab : IsMulCommutative A) (hEA : E ≤ A) (hBA : B ≤ A)
    (_hEB : E ≤ B) [Finite A]
    {y : H} (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hyp : y ^ p = 1)
    (hyΩ : ∀ ω ∈ Work.PGroup.omega1 H p A, y * ω = ω * y)
    (hEinv : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hΩE : Work.PGroup.omega1 H p A ≤ E)
    (hBI : ⁅Subgroup.zpowers y, B⁆ ≤ E)
    (hEI : ⁅E, Subgroup.zpowers y⁆ ≤ Work.PGroup.omega1 H p A) :
    ⁅B, Subgroup.zpowers y⁆ ≤ Work.PGroup.omega1 H p A := by
  set Ω := Work.PGroup.omega1 H p A with hΩ
  set B₀ : Subgroup H := E ⊔ Subgroup.zpowers y with hB₀
  set C : Subgroup H := Ω ⊔ Subgroup.zpowers y with hC
  haveI : Finite ↥E := Finite.of_injective (Subgroup.inclusion hEA) (Subgroup.inclusion_injective hEA)
  haveI : Finite ↥Ω := Finite.of_injective (Subgroup.inclusion (Work.PGroup.omega1_le p A))
    (Subgroup.inclusion_injective (Work.PGroup.omega1_le p A))
  have hΩA : Ω ≤ A := Work.PGroup.omega1_le p A
  have hΩeq : Ω = Work.PGroup.omega p 1 A := by rw [hΩ, Work.PGroup.omega_one_eq_omega1]
  have hCeq : C = Work.PGroup.omega1 H p B₀ := by
    have h := omega1_sup_zpowers_eq (p := p) (A := A) (E := E) (y := y) hp hpodd hAab hEA
      hyA hyp hyΩ hEinv hΩE hEI
    rw [hC, hB₀, hΩ]
    exact h.symm
  have hComega : C = Work.PGroup.omega p 1 B₀ := by
    rw [hCeq, Work.PGroup.omega_one_eq_omega1]
  -- `B ≤ N(B₀)`
  have hNB : B ≤ Subgroup.normalizer (B₀ : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb z hz
    rw [hB₀] at hz ⊢
    obtain ⟨e, he, j, hje⟩ := mem_sup_zpowers_of_finite (E := E) hEinv hz
    have hbj : ⁅b, y ^ j⁆ ∈ E := by
      have hle : ⁅B, Subgroup.zpowers y⁆ ≤ E := by
        rw [Subgroup.commutator_comm]; exact hBI
      exact Subgroup.commutator_le.mp hle b hb (y ^ j)
        (Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) j)
    rw [← hje]
    have hbe : b * e * b⁻¹ = e := by
      have hc : Commute e b := by rw [commute_iff_eq]; exact setLike_mul_comm (hEA he) (hBA hb)
      rw [← hc.eq]; group
    have hbyj : b * y ^ j * b⁻¹ = ⁅b, y ^ j⁆ * y ^ j := by
      rw [commutatorElement_def]; group
    have hkey : b * (e * y ^ j) * b⁻¹ = e * (⁅b, y ^ j⁆ * y ^ j) := by
      rw [show b * (e * y ^ j) * b⁻¹ = (b * e * b⁻¹) * (b * y ^ j * b⁻¹) from by group,
        hbe, hbyj]
    rw [hkey]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hbj)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j)))
  -- `⟨y⟩ ≤ N(B₀)`
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (B₀ : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz b hb
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [hB₀] at hb ⊢
    obtain ⟨e, he, j, hje⟩ := mem_sup_zpowers_of_finite (E := E) hEinv hb
    rw [← hje]
    have h1 : y ^ t * e * y ^ (-t) ∈ E := conj_zpow_mem_of_finite hEinv he t
    have h2 : y ^ t * y ^ j * (y ^ t)⁻¹ = y ^ j := by
      rw [show (y ^ t)⁻¹ = y ^ (-t) by rw [zpow_neg], ← zpow_add, ← zpow_add]
      congr 1; ring
    have hkey : y ^ t * (e * y ^ j) * (y ^ t)⁻¹
        = (y ^ t * e * y ^ (-t)) * y ^ j := by
      rw [show y ^ t * (e * y ^ j) * (y ^ t)⁻¹
          = (y ^ t * e * y ^ (-t)) * (y ^ t * y ^ j * (y ^ t)⁻¹) from by
        rw [show (y ^ t)⁻¹ = y ^ (-t) by rw [zpow_neg]]; group, h2]
    rw [hkey]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j))
  have hNB₀ : B₀ ≤ Subgroup.normalizer (B₀ : Set H) := Subgroup.le_normalizer
  -- `B₁ ≤ N(C)`
  have hconjC : ∀ x ∈ Subgroup.normalizer (B₀ : Set H),
      x ∈ Subgroup.normalizer (C : Set H) := by
    intro x hxB₀
    have hconj : Work.PGroup.conjBy x (Work.PGroup.omega p 1 B₀) = Work.PGroup.omega p 1 B₀ :=
      Work.PGroup.omega_conj p 1 B₀ x hxB₀
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (B₀ : Set H) := Subgroup.inv_mem _ hxB₀
    have hconj' : Work.PGroup.conjBy x⁻¹ (Work.PGroup.omega p 1 B₀) = Work.PGroup.omega p 1 B₀ :=
      Work.PGroup.omega_conj p 1 B₀ x⁻¹ hxinv
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      have hmem : MulAut.conj x c ∈ Work.PGroup.conjBy x (Work.PGroup.omega p 1 B₀) :=
        Set.mem_smul_set.mpr ⟨c, by rw [← hComega]; exact hc, rfl⟩
      rw [hconj] at hmem
      rwa [show MulAut.conj x c = x * c * x⁻¹ from rfl, ← hComega] at hmem
    · intro hc
      have hmem : MulAut.conj x⁻¹ (x * c * x⁻¹) ∈
          Work.PGroup.conjBy x⁻¹ (Work.PGroup.omega p 1 B₀) :=
        Set.mem_smul_set.mpr ⟨x * c * x⁻¹, by rw [← hComega]; exact hc, rfl⟩
      rw [hconj'] at hmem
      have h3 : MulAut.conj x⁻¹ (x * c * x⁻¹) = c := by
        rw [show MulAut.conj x⁻¹ (x * c * x⁻¹) = x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ from rfl]; group
      rw [h3] at hmem
      rwa [← hComega] at hmem
  have hNC : B ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (C : Set H) := by
    refine sup_le ?_ ?_
    · intro b hb; exact hconjC b (hNB hb)
    · intro z hz; exact hconjC z (hyN hz)
  -- `y` preserves `Ω`
  have hyΩinv : ∀ ω ∈ Ω, y * ω * y⁻¹ ∈ Ω := by
    intro ω hω
    rw [show y * ω * y⁻¹ = ω by rw [hyΩ ω hω]; group]
    exact hω
  -- `A ∩ C = Ω`
  have hAC : A ⊓ C = Ω := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzA, hzC⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨ω, hω, t, hωt⟩ := mem_sup_zpowers_of_finite (E := Ω) hyΩinv hzC
      have hytA : y ^ t ∈ A := by
        have h2 : ω⁻¹ * z = y ^ t := by rw [← hωt]; group
        rw [← h2]
        exact A.mul_mem (A.inv_mem (hΩA hω)) hzA
      have hytΩ : y ^ t ∈ Ω := by
        rw [mem_omega1_iff hAab]
        refine ⟨hytA, ?_⟩
        have h1 : (y ^ t) ^ p = (y ^ t) ^ (p : ℤ) := by rw [zpow_natCast]
        rw [h1, ← zpow_mul, mul_comm t (p : ℤ), zpow_mul, zpow_natCast, hyp, one_zpow]
      rw [← hωt]
      exact Ω.mul_mem hω hytΩ
    · intro z hz
      exact Subgroup.mem_inf.mpr ⟨hΩA hz, Subgroup.mem_sup_left hz⟩
  rw [Subgroup.commutator_le]
  intro b hb z hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hbA : b ∈ A := hBA hb
  have hbyb : b * y * b⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.mp (hNC (Subgroup.mem_sup_left hb)) y).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hkey : ⁅b, y ^ j⁆ = (b * y * b⁻¹) ^ j * y ^ (-j) := by
    rw [commutatorElement_def, conj_zpow, show (y ^ j)⁻¹ = y ^ (-j) by rw [zpow_neg]]
  have hmemA : ⁅b, y ^ j⁆ ∈ A := by
    have h1 : y ^ j * b⁻¹ * y ^ (-j) ∈ A :=
      conj_zpow_mem_of_finite (E := A) hyA (A.inv_mem hbA) j
    rw [commutatorElement_def]
    have h2 : b * y ^ j * b⁻¹ * (y ^ j)⁻¹ = b * (y ^ j * b⁻¹ * y ^ (-j)) := by
      rw [show (y ^ j)⁻¹ = y ^ (-j) by rw [zpow_neg]]; group
    rw [h2]
    exact A.mul_mem hbA h1
  have hmemC : ⁅b, y ^ j⁆ ∈ C := by
    rw [hkey]
    exact C.mul_mem (Subgroup.zpow_mem C hbyb j)
      (Subgroup.zpow_mem C (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) (-j))
  exact hAC ▸ Subgroup.mem_inf.mpr ⟨hmemA, hmemC⟩


end Work.LocalPrelim
