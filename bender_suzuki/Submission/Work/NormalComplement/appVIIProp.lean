import Submission.Work.NormalComplement.AppVIIBase
import Submission.Work.GroupTheory.SylowIUnionTop
import Submission.Work.Hering.Step5.appVII_conj
import Submission.Work.NormalComplement.AppVII.SimpleFixedPoint
import Submission.Work.NormalComplement.AppVII.ExistsConstituent
import Submission.Work.NormalComplement.AppVII.ExtraspecialData
import Submission.Work.NormalComplement.AppVII.AbelianCent
import Submission.Work.NormalComplement.AppVII.AbelianKernelCase
import Submission.Work.NormalComplement.AppVII.ElementaryOfIrreducible
import Submission.Work.NormalComplement.AppVII.GroupStructure
import Submission.Work.Hering.AppVII.special_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Appendix VII, in the ambient form needed by area `NormalComplement`

This module proves `Work.NormalComplement.Design.AppVIIProp` on top of the machinery in
`Submission/Work/NormalComplement/AppVIIBase.lean`.

The abstract form `AbstractAppVII` is proved by strong induction on `|A| · |K|`.  Besides the
"collapse" steps (`Φ(K) ≠ 1`, `K'` proper nontrivial) the two structural steps are

* `K` abelian with `Φ(K) = 1`: proved as `abelianCaseAux` below, from the pieces
  `GroupStructure`, `special_abelian`, `AbelianCent`, `AbelianKernelCase`,
  `ElementaryOfIrreducible`, `ExtraspecialData`, `ExistsConstituent` and `SimpleFixedPoint`
  (Peterfalvi's special configuration: `Q` a `q`-group, `[Q,P] = Q`, `Φ(Q) ≤ Z(Q)`, then `Q`
  abelian or extraspecial, contradicted by `special_abelian` resp. `SimpleFixedPoint`);
* `K` perfect (so `K` is not solvable, `K` not a `p`-group, and hence `|A|` is odd): every
  `A`-invariant Sylow of `K` is proper, so it is fixed pointwise by `⁅P,Q⁆` by the induction
  hypothesis, and these Sylows generate `K` (`trivialOn_of_invariant_sylow`).
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement
open FT
open Submission.Blueprint

namespace Work.NormalComplement

/-! ## An independent route through the abelian case

The declarations below assemble the abelian case out of the small proved pieces of this
workspace, so that the only inputs from the "special configuration" are `GroupStructure`,
`special_abelian`, `AbelianCent`, `AbelianKernelCase`, `ElementaryOfIrreducible`,
`ExtraspecialData`, `ExistsConstituent` and `SimpleFixedPoint`. -/

/-- If `Z(Q) = [Q,Q]` and `⁅P,Q⁆ = Q ≠ ⊥` then `Q` is not commutative. -/
theorem not_commutative_of_center_eq_commutator {A : Type*} [Group A] (P Q : Subgroup A)
    (hPQ : ⁅P, Q⁆ = Q) (hR : ⁅P, Q⁆ ≠ ⊥)
    (hZeq : Subgroup.center ↥Q = ⁅(⊤ : Subgroup ↥Q), ⊤⁆) : ¬ IsMulCommutative ↥Q := by
  intro hab
  haveI : IsMulCommutative ↥Q := hab
  have hZtop : Subgroup.center ↥Q = ⊤ := Subgroup.center_eq_top
  have hcbot : ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ = ⊥ := by
    rw [← commutator_def ↥Q]
    exact (commutator_eq_bot_iff ↥Q).mpr hab
  have htopbot : (⊤ : Subgroup ↥Q) = ⊥ := by rw [← hZtop, hZeq, hcbot]
  have hQbot : Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    have hmem : (⟨q, hq⟩ : ↥Q) ∈ (⊤ : Subgroup ↥Q) := Subgroup.mem_top _
    rw [htopbot] at hmem
    simpa using hmem
  exact hR (by rw [hPQ, hQbot])

/-- **The extraspecial branch of the special configuration.**  `ExistsConstituent` produces an
irreducible `F̄_r[A]`-module whose `P`-fixed vectors vanish, while `SimpleFixedPoint` (Peterfalvi's
Part 2 computation) produces one. -/
theorem corner_extraspecial {A : Type*} [Group A] [Finite A] (Q P : Subgroup A)
    (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p q m : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hQcard : Nat.card ↥Q = q ^ (2 * m + 1)) (hm : 1 ≤ m) (hqodd : Odd q)
    (hQext : Work.PGroup.IsExtraspecial q (⊤ : Subgroup ↥Q))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set A) = (Subgroup.center ↥Q).map Q.subtype)
    (hcomm : ⁅P, Q⁆ = Q)
    {K : Type*} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) {r : ℕ} (hr : r.Prime)
    (hKexp : ∀ x : K, x ^ r = 1) (hKcomm : IsMulCommutative K) (hKne : Nontrivial K)
    (hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1)
    (hPfpf : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hQfix : ∀ k : K, (∀ a ∈ Q, a • k = k) → k = 1) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype ↥Q := Fintype.ofFinite ↥Q
  letI : Fintype ↥P := Fintype.ofFinite ↥P
  have hrK : r ∣ Nat.card K := by
    obtain ⟨x, hx⟩ := exists_ne (1 : K)
    have h1 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hKexp x)
    have h2 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
    have h3 : orderOf x = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf x) h1 with h | h
      · exact absurd h h2
      · exact h
    rw [← h3]; exact orderOf_dvd_natCard x
  have hrA : Nat.Coprime r (Nat.card A) := hcop.coprime_dvd_left hrK
  obtain ⟨V, _, _, _, ρ, hirrρ, hZ, hfix⟩ :=
    (Work.NormalComplement.AppVII.ExistsConstituent Q P hQn hinf hsup hp hq hcardP hpQ hQcard
      hm hQext hCQ hcop hKexp hKcomm hKne hirr hfaith hPfpf :
      ∃ (V : Type) (_ : AddCommGroup V)
        (_ : Module (AlgebraicClosure (ZMod r)) V)
        (_ : Module.Finite (AlgebraicClosure (ZMod r)) V)
        (ρ : Representation (AlgebraicClosure (ZMod r)) A V),
        ρ.IsIrreducible ∧ (¬ (Subgroup.center ↥Q).map Q.subtype ≤ ρ.ker) ∧
        (∀ v : V, (∀ s ∈ P, ρ s v = v) → v = 0))
  letI : ρ.IsIrreducible := hirrρ
  obtain ⟨v, hvne, hvp⟩ :=
    Work.NormalComplement.AppVII.SimpleFixedPoint Q P hQn hinf hsup hp hq hqodd hcardP hpQ
      hQcard hm hQext hCQ hcomm hrA ρ hZ
  exact hvne (hfix v hvp)

/-- **Peterfalvi's special configuration is impossible.**  This is the special case of the
Appendix in which `K` is a non-trivial elementary abelian `r`-group and `QP` acts on it
faithfully and irreducibly, `C_K(P) = C_K(Q) = 1`, and `P` centralises every proper
`P`-invariant subgroup of `Q`. -/
theorem special_config_aux {A : Type*} [Group A] [Finite A] {K : Type*} [Group K] [Finite K]
    [MulDistribMulAction A K] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hR : ⁅P, Q⁆ ≠ ⊥)
    (hKelem : ∃ r : ℕ, r.Prime ∧ ∀ x : K, x ^ r = 1)
    (hKcomm : IsMulCommutative K) (hKne : Nontrivial K)
    (hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1)
    (hPfpf : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hQfix : ∀ k : K, (∀ a ∈ Q, a • k = k) → k = 1)
    (hcent : ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥) :
    False := by
  classical
  obtain ⟨r, hr, hKexp⟩ := hKelem
  have hcopPQ : (Nat.card ↥P).Coprime (Nat.card ↥Q) := by
    rw [hcardP]; exact hp.coprime_iff_not_dvd.mpr hpQ
  obtain ⟨hPQ, hQp, hPhi, hdich⟩ := Work.NormalComplement.AppVII.GroupStructure P Q hQn hinf hsup hp hcardP hpQ hR hcent
  rcases hdich with hQab | ⟨hZeq, hZle⟩
  · -- `Q` commutative: the Frobenius (orbit-sum) contradiction of `special_abelian`.
    have hAB : Q ⊓ Subgroup.centralizer (P : Set A) = ⊥ := by
      have hc := Work.NormalComplement.AppVII.centralizer_inf_le_commutator P Q hQn hcopPQ hPQ
      have hQQ : ⁅Q, Q⁆ = ⊥ := by
        rw [← Subgroup.map_subtype_commutator Q, (commutator_eq_bot_iff ↥Q).mpr hQab,
          Subgroup.map_bot]
      rw [inf_comm]
      exact eq_bot_iff.mpr (hc.trans (le_of_eq hQQ))
    exact Work.Hering.AppVII.special_abelian P Q hQn hinf hsup hp hcardP hpQ hPQ hQab hAB
      hcop hr hKexp hKcomm hKne hirr hfaith hPfpf hQfix
  · -- `Q` non-commutative: `Q` is extraspecial and Part 2 applies.
    have hQnab : ¬ IsMulCommutative ↥Q :=
      not_commutative_of_center_eq_commutator P Q hPQ hR hZeq
    obtain ⟨q, hq, hQpq⟩ := hQp
    have hCQ : Q ⊓ Subgroup.centralizer (P : Set A) = (Subgroup.center ↥Q).map Q.subtype := by
      refine le_antisymm ?_ (le_inf (Subgroup.map_subtype_le (Subgroup.center ↥Q)) hZle)
      have hQQ : ⁅Q, Q⁆ = (Subgroup.center ↥Q).map Q.subtype := by
        rw [← Subgroup.map_subtype_commutator Q, commutator_def, ← hZeq]
      have h1 : Subgroup.centralizer (P : Set A) ⊓ Q ≤ ⁅Q, Q⁆ :=
        Work.NormalComplement.AppVII.centralizer_inf_le_commutator P Q hQn hcopPQ hPQ
      rw [hQQ] at h1
      intro x hx
      exact h1 (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, (Subgroup.mem_inf.mp hx).1⟩)
    obtain ⟨hqodd, ⟨m, hm, hQcard, hQext⟩⟩ :=
      Work.NormalComplement.AppVII.ExtraspecialData P Q hQn hinf hsup hp hq hcardP hpQ hQpq
        hPQ hQnab hZeq hPhi hCQ hodd hcop hr hKexp hKcomm hKne hirr hfaith
    exact corner_extraspecial Q P hQn hinf hsup hp hq hcardP hpQ hQcard hm hqodd hQext hCQ hPQ
      hcop hr hKexp hKcomm hKne hirr hfaith hPfpf hQfix

/-- **The abelian case of Appendix VII** (Peterfalvi, Part 1, steps 1–4): if `K` is abelian with
`Φ(K) = 1` and `C_K(P) = 1` then `⁅P,Q⁆` acts trivially on `K`. -/
theorem abelianCaseAux {n : ℕ} (hFT : FeitThompsonProp) (ih : ∀ m < n, AbstractAppVII m)
    {A : Type} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hfix : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hsize : Nat.card A * Nat.card K = n)
    (hcomm : commutator K = ⊥) (hPhi : frattini K = ⊥)
    (hR : ⁅P, Q⁆ ≠ ⊥) (hnt : Nontrivial K) :
    ∀ k : K, ∀ a ∈ ⁅P, Q⁆, a • k = k := by
  classical
  haveI hKcomm : IsMulCommutative K := (commutator_eq_bot_iff K).mp hcomm
  have hsol : Group.IsSolvable A ∨ Group.IsSolvable K := solvable_of_coprime hFT hcop
  by_cases hex : ∃ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) ∧ M ≠ ⊥ ∧ M ≠ ⊤
  · obtain ⟨M, hMinv, hMbot, hMtop⟩ := hex
    haveI : M.Normal := Subgroup.normal_of_isMulCommutative M
    haveI : FT.IsInvariant A M := ⟨fun a => by
      refine le_antisymm ?_ ?_
      · intro y hy
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
        have h1 := hMinv a (a⁻¹ • y) hy
        rwa [smul_inv_smul] at h1
      · intro y hy
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        exact hMinv a⁻¹ y hy⟩
    exact collapse hFT ih P Q hQn hinf hsup hp hcardP hpQ hodd hcop hfix hsize hsol M hMbot hMtop
  · push_neg at hex
    obtain ⟨r, hr, hKexp⟩ := Work.NormalComplement.AppVII.ElementaryOfIrreducible (A := A) hKcomm hPhi hnt hex
    let φ : A →* MulAut K := MulDistribMulAction.toMulAut A K
    have hφker : ∀ a : A, a ∈ φ.ker ↔ (∀ x : K, a • x = x) := by
      intro a
      rw [MonoidHom.mem_ker]
      constructor
      · intro h x
        have h2 : (MulDistribMulAction.toMulAut A K a) x = (1 : MulAut K) x := by rw [h]
        simpa using h2
      · intro h
        ext x
        rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
        exact h x
    have hfaith_of : φ.ker = ⊥ → (∀ a : A, (∀ x : K, a • x = x) → a = 1) := by
      intro hk a ha
      rw [← Subgroup.mem_bot, ← hk]
      exact (hφker a).mpr ha
    let T : Subgroup K :=
      { carrier := {k : K | ∀ a ∈ Q, a • k = k}
        mul_mem' := by intro x y hx hy a ha; rw [smul_mul', hx a ha, hy a ha]
        one_mem' := by intro a _; exact smul_one a
        inv_mem' := by intro x hx a ha; rw [smul_inv', hx a ha] }
    have hTmem : ∀ k : K, k ∈ T ↔ (∀ a ∈ Q, a • k = k) := fun k => Iff.rfl
    have hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T := by
      intro a x hx
      rw [hTmem] at hx ⊢
      intro q hq
      have hQmem : a⁻¹ * q * a ∈ Q := by simpa using hQn.conj_mem q hq a⁻¹
      have h1 : q • (a • x) = a • ((a⁻¹ * q * a) • x) := by
        rw [← mul_smul, ← mul_smul]; congr 1; group
      rw [h1, hx (a⁻¹ * q * a) hQmem]
    by_cases hker : φ.ker = ⊥
    · -- faithful case: the special configuration is contradictory
      have hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1 := hfaith_of hker
      have hQfix : ∀ k : K, (∀ a ∈ Q, a • k = k) → k = 1 := by
        have hTcase : T = ⊥ ∨ T = ⊤ := by
          rcases eq_or_ne T ⊥ with h | h
          · exact Or.inl h
          · exact Or.inr (hex T hTinv h)
        rcases hTcase with h | h
        · intro k hk
          rw [← Subgroup.mem_bot, ← h]
          exact (hTmem k).mpr hk
        · exfalso
          have hQle : Q ≤ φ.ker := by
            intro a ha
            rw [hφker]
            intro x
            exact (hTmem x).mp (by rw [h]; exact Subgroup.mem_top x) a ha
          have hQbot : Q = ⊥ := by
            rw [hker] at hQle
            exact le_bot_iff.mp hQle
          apply hR
          rw [hQbot]
          exact Subgroup.commutator_bot_right P
      have hcent : ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' →
          ⁅P, Q'⁆ = ⊥ :=
        Work.NormalComplement.AppVII.AbelianCent hFT ih P Q hQn hinf hsup hp hcardP hpQ hodd
          hcop hfix hsize hfaith
      exact (special_config_aux P Q hQn hinf hsup hp hcardP hpQ hodd hcop hR
        ⟨r, hr, hKexp⟩ hKcomm hnt hex hfaith hfix hQfix hcent).elim
    · -- non-faithful case: the action factors through `A ⧸ C_A(K)`
      exact Work.NormalComplement.AppVII.AbelianKernelCase hFT ih P Q hQn hinf hsup hp hcardP
        hpQ hodd hcop hfix hsize hker

/-! ## Reduction to the Sylow subgroups

If a subgroup `B ≤ A` fixes every proper `A`-invariant Sylow subgroup of `K` pointwise and `K`
is not a `p`-group for any prime `p`, then `B` fixes `K` pointwise.  The `A`-invariant Sylows
exist by the coprime Glauberman lemma (`Work.Coprime.exists_invariant_sylow`) and generate `K`. -/

theorem trivialOn_of_invariant_sylow {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    [MulDistribMulAction A K] (B : Subgroup A)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable K)
    (h : ∀ (p : ℕ) (hp : p.Prime) (S : Sylow p K), (∀ a : A, a • (S : Subgroup K) = S) →
        (S : Subgroup K) ≠ ⊤ → ∀ k ∈ (S : Subgroup K), ∀ a ∈ B, a • k = k)
    (hne : ∀ (p : ℕ) (hp : p.Prime), ¬ IsPGroup p K) :
    ∀ k : K, ∀ a ∈ B, a • k = k := by
  classical
  -- choose one `A`-invariant Sylow subgroup per prime, each of them proper
  have hchoice : ∀ (p : ℕ) (hp : p.Prime),
      ∃ S : Sylow p K, (∀ a : A, a • (S : Subgroup K) = S) ∧ (S : Subgroup K) ≠ ⊤ := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨S, hS⟩ := Work.Coprime.exists_invariant_sylow A hcop hsol p
    refine ⟨S, ?_, ?_⟩
    · intro a
      have h1 := congrArg (fun T : Sylow p K => (T : Subgroup K)) (hS a)
      rwa [Sylow.pointwise_smul_def] at h1
    · intro hStop
      refine hne p hp (IsPGroup.of_equiv ?_ Subgroup.topEquiv)
      rw [← hStop]
      exact S.isPGroup'
  choose Sout hSinv hSne using hchoice
  -- the chosen Sylow subgroups generate `K`
  have htop : (⨆ (p : ℕ) (hp : p.Prime), ((Sout p hp : Sylow p K) : Subgroup K)) = ⊤ :=
    Work.GroupTheory.SylowIUnionTop Sout
  -- `B` fixes each of them pointwise, hence `K`
  letI : MulDistribMulAction ↥B K := restrictAction B
  have hle : (⨆ (p : ℕ) (hp : p.Prime), ((Sout p hp : Sylow p K) : Subgroup K)) ≤
      FT.fixedPoints ↥B K := by
    apply iSup_le
    intro p
    apply iSup_le
    intro hp
    intro k hk
    rw [FT.mem_fixedPoints]
    intro b
    show restrictSmul B b k = k
    exact h p hp (Sout p hp) (hSinv p hp) (hSne p hp) k hk (b : A) b.2
  intro k a ha
  have htop' : (⊤ : Subgroup K) ≤ FT.fixedPoints ↥B K := htop ▸ hle
  have hk : k ∈ FT.fixedPoints ↥B K := htop' (Subgroup.mem_top k)
  have hfin : (⟨a, ha⟩ : ↥B) • k = k := (FT.mem_fixedPoints.mp hk) ⟨a, ha⟩
  have hfin' : restrictSmul B ⟨a, ha⟩ k = k := hfin
  exact hfin'

/-- **The abstract Appendix VII.** -/
theorem abstractAppVII : ∀ n : ℕ, AbstractAppVII n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hFT A _ _ P Q hQn hinf hsup p hp hcardP hpQ hodd K _ _ _ hcop hfix hsize
    have hsol := solvable_of_coprime hFT hcop
    by_cases hKs : Subsingleton K
    · intro k a ha
      exact Subsingleton.elim _ _
    · by_cases hbot : ⁅P, Q⁆ = ⊥
      · intro k a ha
        rw [hbot] at ha
        rw [Subgroup.mem_bot.mp ha, one_smul]
      · by_cases hPhi : frattini K = ⊥
        · -- `Φ(K) = 1`
          by_cases hK' : commutator K = ⊥
          · -- `K` abelian: Peterfalvi's special configuration
            exact abelianCaseAux hFT ih P Q hQn hinf hsup hp hcardP
              hpQ hodd hcop hfix hsize hK' hPhi hbot (not_subsingleton_iff_nontrivial.mp hKs)
          · by_cases hK'top : commutator K = ⊤
            · -- `K` perfect: `K` is not solvable, hence not a `p`-group; every `A`-invariant
              -- Sylow subgroup of `K` is proper and fixed pointwise by the induction hypothesis
              haveI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hKs
              have hne : ∀ (p : ℕ) (hp : p.Prime), ¬ IsPGroup p K := by
                intro q hq hqg
                haveI : Fact q.Prime := ⟨hq⟩
                haveI : Group.IsPerfect K := ⟨hK'top⟩
                haveI : Group.IsNilpotent K := IsPGroup.isNilpotent hqg
                exact Group.IsPerfect.not_isSolvable K inferInstance
              refine trivialOn_of_invariant_sylow ⁅P, Q⁆ hcop.symm hsol ?_ hne
              intro q hq S hSinv hSne k hk a ha
              -- the induction hypothesis applied to the `A`-invariant subgroup `↥S`
              have hSinv' : ∀ a : A, ∀ x ∈ (S : Subgroup K), a • x ∈ (S : Subgroup K) := by
                haveI : FT.IsInvariant A (S : Subgroup K) := ⟨hSinv⟩
                exact fun a x hx => (inferInstance : FT.IsInvariant A (S : Subgroup K)).smul_mem a hx
              letI : MulDistribMulAction A ↥(S : Subgroup K) := subAction (S : Subgroup K) hSinv'
              have hcopS : Nat.Coprime (Nat.card ↥(S : Subgroup K)) (Nat.card A) :=
                Nat.Coprime.coprime_dvd_left
                  (Subgroup.card_subgroup_dvd_card (S : Subgroup K)) hcop
              have hfixS : ∀ x : ↥(S : Subgroup K), (∀ a ∈ P, a • x = x) → x = 1 := by
                intro x hx
                apply Subtype.ext
                apply hfix
                intro b hb
                exact congrArg (fun t : ↥(S : Subgroup K) => (t : K)) (hx b hb)
              have hsizeS : Nat.card A * Nat.card ↥(S : Subgroup K) < n := by
                rw [← hsize]
                refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.card_pos (α := A))
                have h1 : Nat.card ↥(S : Subgroup K) * (S : Subgroup K).index = Nat.card K :=
                  Subgroup.card_mul_index _
                have h2 : 2 ≤ (S : Subgroup K).index := by
                  have hne1 : (S : Subgroup K).index ≠ 1 := fun hh =>
                    hSne (Subgroup.index_eq_one.mp hh)
                  have hpos : 0 < (S : Subgroup K).index :=
                    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
                  omega
                have hpos : 0 < Nat.card ↥(S : Subgroup K) := Nat.card_pos
                nlinarith
              have hres := ih (Nat.card A * Nat.card ↥(S : Subgroup K)) hsizeS hFT A P Q hQn
                hinf hsup hp hcardP hpQ hodd (↥(S : Subgroup K)) hcopS hfixS rfl ⟨k, hk⟩ a ha
              exact congrArg (fun t : ↥(S : Subgroup K) => (t : K)) hres
            · -- collapse with `N = commutator K`
              haveI : (commutator K).Normal := Subgroup.commutator_normal _ _
              haveI : (commutator K).Characteristic := Subgroup.commutator_characteristic _ _
              haveI : FT.IsInvariant A (commutator K) :=
                isInvariant_of_characteristic (commutator K)
              exact collapse hFT ih P Q hQn hinf hsup hp hcardP hpQ hodd hcop hfix hsize hsol
                (commutator K) hK' hK'top
        · -- `Φ(K) ≠ 1`: collapse with `N = Φ(K)`
          haveI : FT.IsInvariant A (frattini K) := isInvariant_of_characteristic (frattini K)
          have hNetop : frattini K ≠ ⊤ := by
            intro h
            exact hKs (Subsingleton.intro fun x y => by
              have h1 : (⊥ : Subgroup K) = ⊤ :=
                frattini_nongenerating (G := K) (K := ⊥) (by rw [h, bot_sup_eq])
              have hx : x ∈ (⊥ : Subgroup K) := h1 ▸ Subgroup.mem_top x
              have hy : y ∈ (⊥ : Subgroup K) := h1 ▸ Subgroup.mem_top y
              rw [Subgroup.mem_bot] at hx hy
              rw [hx, hy])
          exact collapse hFT ih P Q hQn hinf hsup hp hcardP hpQ hodd hcop hfix hsize hsol
            (frattini K) hPhi hNetop

/-- **Peterfalvi I Appendix VII** in the ambient form all three uses in this area need
(`Work.NormalComplement.Design.AppVIIProp`, `_design/Vocab.lean`): `Q ⋊ P` acting by conjugation on
`K` (all inside `G`), `|P| = p` prime, `p ∤ |Q|`, `|C_Q(P)|` odd, `(|K|,|QP|) = 1`; if `C_K(P) = 1`
then `[P,Q]` centralises `K`.  (App. VII: `K = ⟨C_K([P,Q]), C_K(P^x) | x ∈ Q⟩`, and
`C_K(P^x) = C_K(P)^x = 1`.)

`P ⊓ Q = ⊥` follows from `p ∤ |Q|`, and `K ◁ (Q ⊔ P)` from `Q, P ≤ N_G(K)`, so the reduction to
the abstract `MulDistribMulAction` form `Work.Hering.AppVII.Defs.AppVIIProp` with
`A := ↥(Q ⊔ P)` is legitimate. -/
theorem appVIIProp : Work.NormalComplement.Design.AppVIIProp := by
  intro hFT G _ _ K Q P hQK hPK hPQ hPprime hpQ hodd hcop hCKP
  classical
  -- rearranging a conjugation equation
  have key : ∀ a b : G, a * b * a⁻¹ = b → a * b = b * a := by
    intro a b hab
    calc a * b = a * b * a⁻¹ * a := by
          rw [mul_assoc (a * b) a⁻¹ a, inv_mul_cancel, mul_one]
      _ = b * a := by rw [hab]
  have hPL : P ≤ Q ⊔ P := le_sup_right
  have hQL : Q ≤ Q ⊔ P := le_sup_left
  have hNQL : Q ⊔ P ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hPQ
  have hNKL : Q ⊔ P ≤ Subgroup.normalizer (K : Set G) := sup_le hQK hPK
  letI : MulDistribMulAction ↥(Q ⊔ P) ↥K := conjAction (Q ⊔ P) K hNKL
  -- `P ⊓ Q = ⊥`, from `|P| = p` prime and `p ∤ |Q|`
  have hPQbot : P ⊓ Q = ⊥ := by
    have hdvd : Nat.card ↥(P ⊓ Q) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hPprime).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      exact hpQ (h1 ▸ Subgroup.card_dvd_of_le inf_le_right)
  -- the abstract configuration inside `↥(Q ⊔ P)`
  have hQn' : (Q.subgroupOf (Q ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr hNQL
  have hinf' : P.subgroupOf (Q ⊔ P) ⊓ Q.subgroupOf (Q ⊔ P) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx1 : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1
    have hx2 : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
    have h3 : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hPQbot]
      exact Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa using h3)
  have hsup' : P.subgroupOf (Q ⊔ P) ⊔ Q.subgroupOf (Q ⊔ P) = ⊤ :=
    Work.Hering.Step5.sup_subgroupOf_of_sup_eq hPL hQL (by rw [sup_comm])
  have hcardP' : Nat.card ↥(P.subgroupOf (Q ⊔ P)) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hpQ' : ¬ Nat.card P ∣ Nat.card ↥(Q.subgroupOf (Q ⊔ P)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv]
    exact hpQ
  have hodd' : Odd (Nat.card ↥(Q.subgroupOf (Q ⊔ P) ⊓
      Subgroup.centralizer ((P.subgroupOf (Q ⊔ P) : Subgroup ↥(Q ⊔ P)) : Set ↥(Q ⊔ P)))) := by
    rw [Work.Hering.Step5.card_inf_centralizer_subgroupOf hPL hQL]
    exact hodd
  -- `C_K(P) = 1` transfers
  have hfix' : ∀ k : ↥K, (∀ a ∈ P.subgroupOf (Q ⊔ P), a • k = k) → k = 1 := by
    intro k hk
    have hkcent : (k : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyL : y ∈ Q ⊔ P := hPL hy
      have hy' : (⟨y, hyL⟩ : ↥(Q ⊔ P)) ∈ P.subgroupOf (Q ⊔ P) :=
        Subgroup.mem_subgroupOf.mpr hy
      have h1 := hk ⟨y, hyL⟩ hy'
      have h2 : y * (k : G) * y⁻¹ = (k : G) := congrArg (fun t : ↥K => (t : G)) h1
      exact key y (k : G) h2
    have hkb : (k : G) ∈ K ⊓ Subgroup.centralizer (P : Set G) :=
      Subgroup.mem_inf.mpr ⟨k.2, hkcent⟩
    have h3 : (k : G) ∈ (⊥ : Subgroup G) := by rw [← hCKP]; exact hkb
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  -- Appendix VII in the abstract configuration
  have hmain := abstractAppVII (Nat.card ↥(Q ⊔ P) * Nat.card ↥K) hFT ↥(Q ⊔ P)
    (P.subgroupOf (Q ⊔ P)) (Q.subgroupOf (Q ⊔ P)) hQn' hinf' hsup' hPprime hcardP' hpQ'
    hodd' (↥K) hcop hfix' rfl
  -- transport the conclusion back to `G`
  intro y hy
  have hyL : y ∈ Q ⊔ P :=
    ((Subgroup.commutator_mono hPL hQL).trans (Subgroup.commutator_le_self (Q ⊔ P))) hy
  have hy' : (⟨y, hyL⟩ : ↥(Q ⊔ P)) ∈ ⁅P.subgroupOf (Q ⊔ P), Q.subgroupOf (Q ⊔ P)⁆ := by
    rw [← Work.Hering.Step5.commutator_subgroupOf_eq hPL hQL]
    exact Subgroup.mem_subgroupOf.mpr hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h1 := hmain ⟨z, hz⟩ ⟨y, hyL⟩ hy'
  have h2 : y * z * y⁻¹ = z := congrArg (fun t : ↥K => (t : G)) h1
  exact (key y z h2).symm

end Work.NormalComplement
