import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.Coprime.All
import Submission.Work.PGroup.Basic
import Submission.Work.Hering.AppVII.Setup
import Submission.Work.Hering.AppVII.part1_Q_isPGroup_and_frattini
import Submission.Work.Hering.AppVII.special_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Appendix VII: base machinery

Shared machinery for Peterfalvi's Appendix VII in the ambient form needed by area
`NormalComplement`.  The target statement is

`Work.NormalComplement.Design.AppVIIProp`:

`Q ⋊ P` acting by conjugation on `K` (all inside `G`), `|P| = p` prime, `p ∤ |Q|`,
`|C_Q(P)|` odd, `(|K|, |QP|) = 1`; if `C_K(P) = 1` then `[P,Q]` centralises `K`.

## The abstract form

Everything is first proved for a coprime `MulDistribMulAction` of a group `A` with subgroups
`Q ◁ A`, `P ≤ A`, `P ⊓ Q = ⊥`, `P ⊔ Q = ⊤` on a finite group `K` with `C_K(P) = 1`
(`AbstractAppVII` below); the ambient statement is then obtained by taking `A := ↥(Q ⊔ P)` and
acting on `↥K` by conjugation.

## The reduction (Peterfalvi's Part 1)

`AbstractAppVII` is proved by strong induction on `|A| · |K|`.  A minimal counterexample has

* `Φ(K) = 1`;
* `K` abelian;
* `K` an elementary abelian `r`-group;
* `K` irreducible, `C_Q(K) = 1`, and `P` centralising every proper `P`-invariant subgroup of `Q`;

then Peterfalvi's "special configuration" results give a contradiction.  The only place where the
Feit–Thompson hypothesis `hFT` is used is the solvability of `K` (odd order in every application),
which makes the Gaschütz fixed point identity available unconditionally.
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement
open FT
open Submission.Blueprint

namespace Work.NormalComplement

/-! ## The abstract statement -/

/-- Peterfalvi's Appendix VII in the form `C_K(P) = 1 ⟹ [P,Q] ⊆ C(K)`, for an abstract coprime
`MulDistribMulAction` of `A` with `Q ◁ A`, `P ⊓ Q = ⊥`, `P ⊔ Q = ⊤`.  The parameter `n` is
`|A| · |K|`; it is exposed so that the statement can be proved by strong induction. -/
def AbstractAppVII (n : ℕ) : Prop :=
  FeitThompsonProp →
  ∀ (A : Type) [Group A] [Finite A] (P Q : Subgroup A) (_ : Q.Normal)
    (_ : P ⊓ Q = ⊥) (_ : P ⊔ Q = ⊤) {p : ℕ} (_ : p.Prime)
    (_ : Nat.card ↥P = p) (_ : ¬ p ∣ Nat.card ↥Q)
    (_ : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    (K : Type) [Group K] [Finite K] [MulDistribMulAction A K]
    (_ : Nat.Coprime (Nat.card K) (Nat.card A))
    (_ : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1),
    Nat.card A * Nat.card K = n → ∀ k : K, ∀ a ∈ ⁅P, Q⁆, a • k = k

section Transport

variable {G : Type*} [Group G]

/-- The conjugation map `(l, k) ↦ l k l⁻¹` on `↥L × ↥K`, for `L ≤ N_G(K)`. -/
noncomputable def conjSmul (L K : Subgroup G) (h : L ≤ Subgroup.normalizer (K : Set G))
    (l : ↥L) (k : ↥K) : ↥K :=
  ⟨(l : G) * (k : G) * (l : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h l.2) (k : G)).mp k.2⟩

@[simp] theorem conjSmul_coe (L K : Subgroup G) (h : L ≤ Subgroup.normalizer (K : Set G))
    (l : ↥L) (k : ↥K) :
    ((conjSmul L K h l k : ↥K) : G) = (l : G) * (k : G) * (l : G)⁻¹ := rfl


theorem conjSmul_one (L K : Subgroup G) (h : L ≤ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    conjSmul L K h 1 k = k :=
  Subtype.ext (by simp only [conjSmul_coe, Subgroup.coe_one, one_mul, inv_one, mul_one])

theorem conjSmul_mul (L K : Subgroup G) (h : L ≤ Subgroup.normalizer (K : Set G))
    (a b : ↥L) (k : ↥K) :
    conjSmul L K h (a * b) k = conjSmul L K h a (conjSmul L K h b k) :=
  Subtype.ext (by simp only [conjSmul_coe, Subgroup.coe_mul, Subgroup.coe_inv]; group)

theorem conjSmul_smul_one (L K : Subgroup G) (h : L ≤ Subgroup.normalizer (K : Set G))
    (l : ↥L) : conjSmul L K h l 1 = 1 :=
  Subtype.ext (by simp only [conjSmul_coe, Subgroup.coe_one, mul_one, mul_inv_cancel])

theorem conjSmul_smul_mul (L K : Subgroup G) (h : L ≤ Subgroup.normalizer (K : Set G))
    (l : ↥L) (a b : ↥K) :
    conjSmul L K h l (a * b) = conjSmul L K h l a * conjSmul L K h l b :=
  Subtype.ext (by simp only [conjSmul_coe, Subgroup.coe_mul]; group)

/-- Conjugation action of a subgroup `L ≤ N_G(K)` on `↥K`. -/
noncomputable def conjAction (L K : Subgroup G) (h : L ≤ Subgroup.normalizer (K : Set G)) :
    MulDistribMulAction ↥L ↥K where
  smul := conjSmul L K h
  one_smul k := conjSmul_one L K h k
  mul_smul a b k := conjSmul_mul L K h a b k
  smul_one l := conjSmul_smul_one L K h l
  smul_mul l a b := conjSmul_smul_mul L K h l a b

end Transport

/-! ## Solvability of one of two groups of coprime order (Feit–Thompson)

Since `|A|` and `|K|` are coprime, one of them is odd, hence solvable by `FeitThompsonProp`.
This is what makes the (solvability-conditional) Gaschütz fixed-point identity and the
Schur–Zassenhaus lemmas available unconditionally in this setting. -/

theorem solvable_of_coprime (hFT : FeitThompsonProp) {A K : Type} [Group A] [Finite A]
    [Group K] [Finite K] (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) :
    Group.IsSolvable A ∨ Group.IsSolvable K := by
  have hiff : ∀ n : ℕ, Odd n ↔ ¬ (2 : ℕ) ∣ n :=
    fun n => Nat.odd_iff.trans Nat.two_dvd_ne_zero.symm
  by_cases h2A : (2 : ℕ) ∣ Nat.card A
  · right
    refine hFT K ((hiff _).mpr fun h2K => ?_)
    have h1 : (2 : ℕ) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h2K h2A
    omega
  · left
    exact hFT A ((hiff _).mpr h2A)

/-! ## Actions of subgroups, and on invariant subgroups -/

/-- The `↥B`-action on `K` obtained by restricting the `A`-action along `B ≤ A`. -/
def restrictSmul {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K] (B : Subgroup A)
    (b : ↥B) (k : K) : K := (b : A) • k

theorem restrictSmul_one {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (B : Subgroup A) (k : K) : restrictSmul B (1 : ↥B) k = k := by
  rw [restrictSmul, Subgroup.coe_one, one_smul]

theorem restrictSmul_mul {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (B : Subgroup A) (a b : ↥B) (k : K) :
    restrictSmul B (a * b) k = restrictSmul B a (restrictSmul B b k) := by
  rw [restrictSmul, restrictSmul, restrictSmul, Subgroup.coe_mul, mul_smul]

theorem restrictSmul_one_smul {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (B : Subgroup A) (b : ↥B) : restrictSmul B b (1 : K) = 1 := by
  rw [restrictSmul, smul_one]

theorem restrictSmul_mul_smul {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (B : Subgroup A) (b : ↥B) (x y : K) :
    restrictSmul B b (x * y) = restrictSmul B b x * restrictSmul B b y := by
  rw [restrictSmul, restrictSmul, restrictSmul, smul_mul']

noncomputable def restrictAction {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (B : Subgroup A) : MulDistribMulAction ↥B K where
  smul := restrictSmul B
  one_smul k := restrictSmul_one B k
  mul_smul a b k := restrictSmul_mul B a b k
  smul_one b := restrictSmul_one_smul B b
  smul_mul b x y := restrictSmul_mul_smul B b x y

/-- The action of `A` on an `A`-invariant subgroup. -/
def subSmul {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K] (M : Subgroup K)
    (hM : ∀ a : A, ∀ x ∈ M, a • x ∈ M) (a : A) (x : ↥M) : ↥M :=
  ⟨a • (x : K), hM a x x.2⟩

theorem subSmul_one {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (M : Subgroup K) (hM : ∀ a : A, ∀ x ∈ M, a • x ∈ M) (x : ↥M) :
    subSmul M hM 1 x = x :=
  Subtype.ext (by simp [subSmul])

theorem subSmul_mul_smul {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (M : Subgroup K) (hM : ∀ a : A, ∀ x ∈ M, a • x ∈ M) (a b : A) (x : ↥M) :
    subSmul M hM (a * b) x = subSmul M hM a (subSmul M hM b x) :=
  Subtype.ext (by simp [subSmul, mul_smul])

theorem subSmul_smul_one {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (M : Subgroup K) (hM : ∀ a : A, ∀ x ∈ M, a • x ∈ M) (a : A) :
    subSmul M hM a 1 = 1 :=
  Subtype.ext (by simp [subSmul])

theorem subSmul_smul_mul {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (M : Subgroup K) (hM : ∀ a : A, ∀ x ∈ M, a • x ∈ M) (a : A) (x y : ↥M) :
    subSmul M hM a (x * y) = subSmul M hM a x * subSmul M hM a y :=
  Subtype.ext (by simp [subSmul, smul_mul'])

noncomputable def subAction {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (M : Subgroup K) (hM : ∀ a : A, ∀ x ∈ M, a • x ∈ M) : MulDistribMulAction A ↥M where
  smul := subSmul M hM
  one_smul x := subSmul_one M hM x
  mul_smul a b x := subSmul_mul_smul M hM a b x
  smul_one a := subSmul_smul_one M hM a
  smul_mul a x y := subSmul_smul_mul M hM a x y

theorem isInvariant_restrict {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    (B : Subgroup A) (M : Subgroup K) [hM : FT.IsInvariant A M] :
    letI := restrictAction (K := K) B
    FT.IsInvariant ↥B M :=
  ⟨fun b => hM.smul_eq_self (b : A)⟩


/-! ## The engine of the reduction: Claim 1

For `N ◁ K` an `A`-invariant normal subgroup, `C_{K/N}(P) = C_K(P)·N/N = 1` by Gaschütz's
fixed-point identity for the *prime order* group `P`; the induction hypothesis for `K ⧸ N` then
shows that `⁅P,Q⁆` acts trivially on `K ⧸ N`, i.e. `[K, ⁅P,Q⁆] ≤ N`. -/

theorem claim1 {n : ℕ} (hFT : FeitThompsonProp) (ih : ∀ m < n, AbstractAppVII m)
    {A : Type} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hfix : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hsize : Nat.card A * Nat.card K = n)
    (N : Subgroup K) [N.Normal] [FT.IsInvariant A N] (hN : N ≠ ⊥) :
    ∀ k : K, ∀ a ∈ ⁅P, Q⁆, (a • k) * k⁻¹ ∈ N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `P` has prime order, hence is cyclic and solvable
  have hsolP : Group.IsSolvable ↥P := by
    haveI : Fact (Nat.card ↥P).Prime := ⟨hcardP ▸ hp⟩
    haveI : IsCyclic ↥P := isCyclic_of_prime_card rfl
    exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  -- the action of `P` on `K`
  letI : MulDistribMulAction ↥P K := restrictAction P
  haveI : FT.IsInvariant ↥P N := isInvariant_restrict (K := K) P N
  have hcopPK : Nat.Coprime (Nat.card ↥P) (Nat.card K) :=
    (hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card P)).symm
  -- Gaschütz's fixed point identity for `P`
  have hGas := Work.Coprime.fixedPoints_quotient (↥P) hcopPK (Or.inl hsolP) N
  -- `C_K(P) = 1`
  have hfixP : FT.fixedPoints ↥P K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact hfix x fun a ha => (FT.mem_fixedPoints.mp hx) ⟨a, ha⟩
  -- hence `C_{K/N}(P) = 1`
  have hfixN' : ∀ x : K ⧸ N, (∀ a : ↥P, a • x = x) → x = 1 := by
    intro x hx
    have hx'' : x ∈ (FT.fixedPoints ↥P K).map (QuotientGroup.mk' N) := hGas.symm ▸ hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx''
    have hy1 : y = 1 := by
      rw [hfixP] at hy
      simpa using hy
    rw [← hyx, hy1]
    rfl
  have hfixN : ∀ x : K ⧸ N, (∀ a ∈ P, a • x = x) → x = 1 :=
    fun x hx => hfixN' x fun a => hx (a : A) a.2
  -- the quotient is smaller
  have hcopQ : Nat.Coprime (Nat.card (K ⧸ N)) (Nat.card A) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_quotient_dvd_card N) hcop
  have hsizeN : Nat.card A * Nat.card (K ⧸ N) < n := by
    rw [← hsize]
    refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.card_pos (α := A))
    have h1 : Nat.card ↥N * N.index = Nat.card K := Subgroup.card_mul_index N
    have h2 : 1 < Nat.card ↥N := by
      have hne : Nat.card ↥N ≠ 1 := fun h => hN (Subgroup.card_eq_one.mp h)
      have hpos : 0 < Nat.card ↥N := Nat.card_pos
      omega
    have h3 : N.index < Nat.card K := by
      rw [← h1]
      have := Nat.mul_lt_mul_of_pos_right h2 (Nat.pos_of_ne_zero
        (Subgroup.index_ne_zero_of_finite (H := N)))
      simpa using this
    rwa [Subgroup.index_eq_card] at h3
  -- induction hypothesis on `K ⧸ N`
  intro k a ha
  have h := ih (Nat.card A * Nat.card (K ⧸ N)) hsizeN hFT A P Q hQn hinf hsup hp hcardP hpQ hodd
    (K ⧸ N) hcopQ hfixN rfl (QuotientGroup.mk' N k) a ha
  have h2 : ((a • k : K) : K ⧸ N) = (k : K ⧸ N) := by
    rw [← FT.quotient_smul_mk N a k]; exact h
  have h3 : k⁻¹ * (a • k) ∈ N := QuotientGroup.eq.mp h2.symm
  have h4 : (a • k) * k⁻¹ = k * (k⁻¹ * (a • k)) * k⁻¹ := by group
  rw [h4]
  exact Subgroup.Normal.conj_mem (inferInstance : N.Normal) (k⁻¹ * (a • k)) h3 k


/-! ## Solvability transfers -/

theorem solvable_quotient_of {A K : Type} [Group A] [Group K] (N : Subgroup K) [N.Normal]
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable K) :
    Group.IsSolvable A ∨ Group.IsSolvable (K ⧸ N) :=
  hsol.imp id fun h => by haveI := h; exact inferInstance

theorem solvable_subgroup_of {A K : Type} [Group A] [Group K]
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable K) (B : Subgroup A) :
    Group.IsSolvable ↥B ∨ Group.IsSolvable K :=
  hsol.imp (fun h => by haveI := h; exact inferInstance) id

/-! ## Claim 2: the induction hypothesis applied to an invariant subgroup -/

theorem claim2 {n : ℕ} (hFT : FeitThompsonProp) (ih : ∀ m < n, AbstractAppVII m)
    {A : Type} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hfix : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hsize : Nat.card A * Nat.card K = n)
    (M : Subgroup K) (hM : ∀ a : A, ∀ x ∈ M, a • x ∈ M) (hM1 : M ≠ ⊥) (hMtop : M ≠ ⊤) :
    letI := subAction M hM
    ∀ m : ↥M, ∀ a ∈ ⁅P, Q⁆, a • m = m := by
  classical
  letI : MulDistribMulAction A ↥M := subAction M hM
  intro m a ha
  have hcopM : Nat.Coprime (Nat.card ↥M) (Nat.card A) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card M) hcop
  have hfixM : ∀ m : ↥M, (∀ a ∈ P, a • m = m) → m = 1 := by
    intro m hm
    have : (m : K) = 1 := hfix m fun a ha => congrArg Subtype.val (hm a ha)
    exact Subtype.ext this
  have hsizeM : Nat.card A * Nat.card ↥M < n := by
    rw [← hsize]
    refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.card_pos (α := A))
    have hlt : Nat.card ↥M < Nat.card K := by
      have h1 : Nat.card ↥M * M.index = Nat.card K := Subgroup.card_mul_index M
      have h2 : 2 ≤ M.index := by
        have hne : M.index ≠ 1 := fun h => hMtop (Subgroup.index_eq_one.mp h)
        have hpos : 0 < M.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        omega
      have hpos : 0 < Nat.card ↥M := Nat.card_pos
      nlinarith
    omega
  exact ih (Nat.card A * Nat.card ↥M) hsizeM hFT A P Q hQn hinf hsup hp hcardP hpQ hodd
    (↥M) hcopM hfixM rfl m a ha

/-! ## Gaschütz for `⁅P,Q⁆`, and the "trivial mod `N`, trivial on `N` ⟹ trivial" step -/

theorem gaschutz_R {A : Type} [Group A] [Finite A] (P Q : Subgroup A)
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable K)
    (N : Subgroup K) [N.Normal] [FT.IsInvariant A N] :
    letI := restrictAction (K := K) ⁅P, Q⁆
    letI := isInvariant_restrict (K := K) ⁅P, Q⁆ N
    (FT.fixedPoints ↥⁅P, Q⁆ K).map (QuotientGroup.mk' N) = FT.fixedPoints ↥⁅P, Q⁆ (K ⧸ N) := by
  letI : MulDistribMulAction ↥⁅P, Q⁆ K := restrictAction ⁅P, Q⁆
  haveI : FT.IsInvariant ↥⁅P, Q⁆ N := isInvariant_restrict (K := K) ⁅P, Q⁆ N
  have hcopR : Nat.Coprime (Nat.card ↥⁅P, Q⁆) (Nat.card K) :=
    (hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card ⁅P, Q⁆)).symm
  exact Work.Coprime.fixedPoints_quotient (↥⁅P, Q⁆) hcopR
    (solvable_subgroup_of hsol ⁅P, Q⁆) N

/-- **The basic reduction step.**  If `⁅P,Q⁆` acts trivially on an `A`-invariant normal `N ◁ K`
and also on `K ⧸ N`, then it acts trivially on `K`. -/
theorem trivialOn_of_le_fixedPoints {A : Type} [Group A] [Finite A] (P Q : Subgroup A)
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable K)
    (N : Subgroup K) [N.Normal] [FT.IsInvariant A N]
    (hN : N ≤ FT.fixedPoints ↥⁅P, Q⁆ K)
    (hK : ∀ k : K, ∀ a ∈ ⁅P, Q⁆, (a • k) * k⁻¹ ∈ N) :
    ∀ k : K, ∀ a ∈ ⁅P, Q⁆, a • k = k := by
  letI : MulDistribMulAction ↥⁅P, Q⁆ K := restrictAction ⁅P, Q⁆
  haveI : FT.IsInvariant ↥⁅P, Q⁆ N := isInvariant_restrict (K := K) ⁅P, Q⁆ N
  have hGas := gaschutz_R (K := K) P Q hcop hsol N
  -- `⁅P,Q⁆` acts trivially on the quotient
  have hquot : ∀ z : K ⧸ N, ∀ a : ↥⁅P, Q⁆, a • z = z := by
    intro z a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N z
    change a • ((k : K ⧸ N)) = (k : K ⧸ N)
    rw [FT.quotient_smul_mk]
    refine QuotientGroup.eq.mpr ?_
    have h1 : ((a : A) • k) * k⁻¹ ∈ N := hK k (a : A) a.2
    change ((a : A) • k)⁻¹ * k ∈ N
    have h2 : ((a : A) • k)⁻¹ * k = k⁻¹ * (((a : A) • k) * k⁻¹)⁻¹ * k := by group
    rw [h2]
    simpa using Subgroup.Normal.conj_mem (inferInstance : N.Normal)
      (((a : A) • k) * k⁻¹)⁻¹ (N.inv_mem h1) k⁻¹
  have hfixed : FT.fixedPoints ↥⁅P, Q⁆ (K ⧸ N) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    exact FT.mem_fixedPoints.mpr (hquot z)
  intro k a ha
  have h2 : (QuotientGroup.mk' N k) ∈ (FT.fixedPoints ↥⁅P, Q⁆ K).map (QuotientGroup.mk' N) := by
    rw [hGas]
    exact hfixed ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp h2
  have hy1 : y⁻¹ * k ∈ N := QuotientGroup.eq.mp hyk
  have h3 : y⁻¹ * k ∈ FT.fixedPoints ↥⁅P, Q⁆ K := hN hy1
  have h4 : y * (y⁻¹ * k) = k := by group
  have : k ∈ FT.fixedPoints ↥⁅P, Q⁆ K := by
    rw [← h4]
    exact Subgroup.mul_mem _ hy h3
  exact (FT.mem_fixedPoints.mp this) ⟨a, ha⟩


/-! ## The collapse tool and the induction -/

/-- A characteristic subgroup is invariant under any group action by automorphisms. -/
theorem isInvariant_of_characteristic {A K : Type*} [Group A] [Group K]
    [MulDistribMulAction A K] (H : Subgroup K) [hH : H.Characteristic] :
    FT.IsInvariant A H := by
  refine ⟨fun a => le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change (MulDistribMulAction.toMulAut A K a).toMonoidHom y ∈ H
    rw [← Subgroup.mem_comap, Subgroup.Characteristic.fixed hH]
    exact hy
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨(MulDistribMulAction.toMulAut A K a).symm x, ?_, ?_⟩
    · change (MulDistribMulAction.toMulAut A K a).symm.toMonoidHom x ∈ H
      rw [← Subgroup.mem_comap, Subgroup.Characteristic.fixed hH]
      simpa using hx
    · simp

/-- **The collapse.**  If `N ◁ K` is a proper, nontrivial `A`-invariant subgroup, then
`[K, ⁅P,Q⁆] ≤ N` (claim 1) and `[N, ⁅P,Q⁆] = 1` (claim 2) force `⁅P,Q⁆` to act trivially on `K`,
by Gaschütz for `⁅P,Q⁆`. -/
theorem collapse {n : ℕ} (hFT : FeitThompsonProp) (ih : ∀ m < n, AbstractAppVII m)
    {A : Type} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hfix : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hsize : Nat.card A * Nat.card K = n)
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable K)
    (N : Subgroup K) [N.Normal] [FT.IsInvariant A N] (hN : N ≠ ⊥) (hNtop : N ≠ ⊤) :
    ∀ k : K, ∀ a ∈ ⁅P, Q⁆, a • k = k := by
  have h1 := claim1 hFT ih P Q hQn hinf hsup hp hcardP hpQ hodd hcop hfix hsize N hN
  have h2 := claim2 hFT ih P Q hQn hinf hsup hp hcardP hpQ hodd hcop hfix hsize N
    (fun a x hx => (inferInstance : FT.IsInvariant A N).smul_mem a hx) hN hNtop
  have hNle : N ≤ FT.fixedPoints ↥⁅P, Q⁆ K := by
    intro x hx
    rw [FT.mem_fixedPoints]
    intro a
    have h3 := h2 ⟨x, hx⟩ (a : A) a.2
    exact congrArg Subtype.val h3
  exact trivialOn_of_le_fixedPoints P Q hcop hsol N hNle h1

