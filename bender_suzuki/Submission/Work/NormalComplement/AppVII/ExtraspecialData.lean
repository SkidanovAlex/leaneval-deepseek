import Mathlib
import Submission.Work.NormalComplement.AppVIIBase
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.card_extraspecial
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial
import Submission.Work.PGroup.isPGroup_of_isExtraspecial
import Submission.Work.PGroup.commutator_le_frattiniIn
import Submission.Work.PGroup.pow_mem_frattiniIn
import Submission.Work.PGroup.isElementaryAbelian_iff_exponent
import Submission.Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise commutatorElement
open Subgroup

namespace Work.NormalComplement.AppVII

/-! ## Auxiliary lemmas

The targets below are phrased for the group `↥Q` itself, while the hypotheses of
`ExtraspecialData` are phrased for subgroups of the ambient group `A`; the first two lemmas
provide the bridges `Work.PGroup.centerIn ⊤ = Z(G)` and `Work.PGroup.frattiniIn ⊤ = Φ(G)`. -/

/-- `Work.PGroup.centerIn ⊤` is the centre of the group. -/
theorem centerIn_top_eq_center (G : Type*) [Group G] :
    Work.PGroup.centerIn (⊤ : Subgroup G) = Subgroup.center G := by
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro a
    rw [← hzy]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, trivial⟩)
  · intro hy
    refine ⟨⟨y, trivial⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.mp hy (w : G))

/-- The canonical (surjective) inclusion `G →* ↥(⊤ : Subgroup G)`. -/
def topIncl (G : Type*) [Group G] : G →* ↥(⊤ : Subgroup G) where
  toFun g := ⟨g, Subgroup.mem_top g⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem topIncl_surjective (G : Type*) [Group G] : Function.Surjective (topIncl G) :=
  fun x => ⟨(x : G), Subtype.ext rfl⟩

@[simp] theorem topIncl_coe (G : Type*) [Group G] (g : G) :
    ((topIncl G g : ↥(⊤ : Subgroup G)) : G) = g := rfl

/-- `Work.PGroup.frattiniIn ⊤` is the Frattini subgroup of the group. -/
theorem frattiniIn_top_eq_frattini (G : Type*) [Group G] :
    Work.PGroup.frattiniIn (⊤ : Subgroup G) = frattini G := by
  rw [Work.PGroup.frattiniIn]
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact frattini_le_comap_frattini_of_surjective
      (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩) hy
  · intro g hg
    have h : topIncl G g ∈ frattini ↥(⊤ : Subgroup G) :=
      frattini_le_comap_frattini_of_surjective (topIncl_surjective G) hg
    exact Subgroup.mem_map.mpr ⟨topIncl G g, h, rfl⟩

/-- In a finite `q`-group whose centre is its derived subgroup and whose Frattini subgroup lies
in the centre, every element of the centre has `q`-th power `1`: the set of such central elements
is a subgroup, and it contains every commutator because `⁅x,y⁆^q = ⁅x,y^q⁆ = 1`. -/
theorem pow_eq_one_of_mem_center_of_center_eq_commutator {Q : Type*} [Group Q] [Finite Q] {q : ℕ}
    (hq : q.Prime) (hQp : IsPGroup q Q) (hZ : Subgroup.center Q = ⁅(⊤ : Subgroup Q), ⊤⁆)
    (hPhi : frattini Q ≤ Subgroup.center Q) : ∀ z ∈ Subgroup.center Q, z ^ q = 1 := by
  let S : Subgroup Q :=
    { carrier := {w | w ∈ Subgroup.center Q ∧ w ^ q = 1}
      one_mem' := ⟨Subgroup.one_mem _, one_pow q⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨Subgroup.mul_mem _ ha1 hb1, ?_⟩
        have hab : Commute a b := (Subgroup.mem_center_iff.mp ha1 b).symm
        rw [hab.mul_pow, ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨Subgroup.inv_mem _ ha1, ?_⟩
        rw [inv_pow, ha2, inv_one] }
  have hcomm : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    have hcent : ⁅x, y⁆ ∈ Subgroup.center Q := by
      rw [hZ]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    refine ⟨hcent, ?_⟩
    have hcy : Commute y ⁅x, y⁆ := Subgroup.mem_center_iff.mp hcent y
    rw [hcy.commutatorElement_pow_right q]
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hPhi (Work.PGroup.pow_mem_frattini hq hQp y)) x
  intro z hz
  exact (hcomm (hZ ▸ hz)).2

/-- If the centre of `Q` is its derived subgroup and `Q` is not commutative, then the centre is
nontrivial. -/
theorem center_ne_bot_of_center_eq_commutator {Q : Type*} [Group Q]
    (hZ : Subgroup.center Q = ⁅(⊤ : Subgroup Q), ⊤⁆) (hnab : ¬ IsMulCommutative Q) :
    Subgroup.center Q ≠ ⊥ := by
  intro hbot
  exact hnab ((commutator_eq_bot_iff Q).mp (by rw [commutator_def Q, ← hZ]; exact hbot))

/-- **Peterfalvi Appendix VII, step 4: in the non-abelian branch `Q` is extraspecial.**

`A = Q ⋊ P` acts on the elementary abelian `r`-group `K` (`r` prime, `∀ x : K, x^r = 1`, `K`
abelian, `K` nontrivial), faithfully and irreducibly, with `(|K|,|A|) = 1`.  `Q ◁ A`, `P ⊓ Q = ⊥`,
`P ⊔ Q = ⊤`, `|P| = p` prime, `p ∤ |Q|`, `Q` is a `q`-group, `⁅P,Q⁆ = Q`, `Q` is non-abelian,
`Z(Q) = [Q,Q]` and `Φ(Q) ≤ Z(Q)`, and `C_Q(P) = Z(Q)` with `|C_Q(P)|` odd.  Then `q` is odd and
`Q` is extraspecial of order `q^(2m+1)` with `m ≥ 1`.

Route (Peterfalvi p.217, step 4): `Z(Q) ≤ Z(A)` (it centralises `Q` and, by `hCQ`, `P`), so on
the irreducible faithful `𝔽_r[A]`-module `K` the elements of `Z(Q)` act as scalars (Schur's
lemma), hence `Z(Q) ↪ 𝔽_r^*` is **cyclic**.  On the other hand `[a,b]^q = [a,b^q] = 1` for
`a,b ∈ Q` (`Q` has class 2 and `b^q ∈ Φ(Q) ≤ Z(Q)`), so `Z(Q) = [Q,Q]` has exponent `q`; a
nontrivial cyclic group of exponent `q` has order `q`.  With `Z(Q) = [Q,Q] = Φ(Q)` (from `hZ`,
`hPhi` and Burnside's basis theorem `⁅Q,Q⁆ ≤ Φ(Q)` for a `q`-group) this says exactly
`Work.PGroup.IsExtraspecial q ⊤`, and `Work.PGroup.card_extraspecial` gives `|Q| = q^(2m+1)`,
`m ≥ 1`; `|Z(Q)| = q` together with `hCQ` and `hodd` gives `Odd q`. -/
theorem ExtraspecialData {A : Type*} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q) (hQp : IsPGroup q ↥Q)
    (hcomm : ⁅P, Q⁆ = Q) (hQnab : ¬ IsMulCommutative ↥Q)
    (hZ : Subgroup.center ↥Q = ⁅(⊤ : Subgroup ↥Q), ⊤⁆)
    (hPhi : frattini ↥Q ≤ Subgroup.center ↥Q)
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set A) = (Subgroup.center ↥Q).map Q.subtype)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type*} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) {r : ℕ} (hr : r.Prime)
    (hKexp : ∀ x : K, x ^ r = 1) (hKcomm : IsMulCommutative K) (hKne : Nontrivial K)
    (hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1) :
    Odd q ∧ ∃ m : ℕ, 1 ≤ m ∧ Nat.card ↥Q = q ^ (2 * m + 1) ∧
      Work.PGroup.IsExtraspecial q (⊤ : Subgroup ↥Q) := by
  classical
  -- Step 1: every element of `Z(Q)` commutes with all of `A`
  have hcentA : ∀ z : ↥Q, z ∈ Subgroup.center ↥Q → ∀ a : A, (z : A) * a = a * (z : A) := by
    intro z hz a
    have hzP : (z : A) ∈ Subgroup.centralizer (P : Set A) := by
      have h1 : (z : A) ∈ Q ⊓ Subgroup.centralizer (P : Set A) := by
        rw [hCQ]
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      exact h1.2
    have htop : Subgroup.centralizer ({(z : A)} : Set A) = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← hsup]
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp hzP x hx).symm
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have h := Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hz (⟨x, hx⟩ : ↥Q))
        simpa using h.symm
    exact Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top a) (z : A)
      (Set.mem_singleton _)
  -- Step 2: the centre of `Q` acts fixed-point-freely on `K`
  have hfp : ∀ z : ↥(Subgroup.center ↥Q), z ≠ 1 → ∀ k : K, (z : A) • k = k → k = 1 := by
    intro z hz k hk
    let M : Subgroup K :=
      { carrier := {k : K | (z : A) • k = k}
        one_mem' := by
          show (z : A) • (1 : K) = 1
          rw [smul_one]
        mul_mem' := by
          intro x y hx hy
          show (z : A) • (x * y) = x * y
          rw [smul_mul', hx, hy]
        inv_mem' := by
          intro x hx
          show (z : A) • x⁻¹ = x⁻¹
          calc (z : A) • x⁻¹
              = ((z : A) • x)⁻¹ := map_inv (MulDistribMulAction.toMulAut A K (z : A)) x
            _ = x⁻¹ := by rw [hx] }
    have hMinv : ∀ a : A, ∀ x ∈ M, a • x ∈ M := by
      intro a x hx
      show (z : A) • (a • x) = a • x
      rw [← mul_smul, hcentA z z.2 a, mul_smul, hx]
    have hkM : k ∈ M := hk
    by_cases hM : M = ⊥
    · rw [hM, Subgroup.mem_bot] at hkM
      exact hkM
    · exfalso
      have htop : M = ⊤ := hirr M hMinv hM
      have hz1 : (z : A) = 1 := hfaith _ fun x => by
        have : x ∈ M := by rw [htop]; trivial
        exact this
      exact hz (Subtype.ext (Subtype.ext hz1))
  -- Step 3: `Z(Q)` is cyclic
  have hQpC : IsPGroup q ↥(Subgroup.center ↥Q) :=
    isPGroup_iff_pow_pow_eq_one.mpr fun z =>
      let ⟨n, hn⟩ := hQp (z : ↥Q)
      ⟨n, Subtype.ext hn⟩
  haveI : IsMulCommutative ↥(Subgroup.center ↥Q) := inferInstance
  have hcyc : IsCyclic ↥(Subgroup.center ↥Q) :=
    Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic hq hQpC
      ((MulDistribMulAction.toMulAut A K).comp (Q.subtype.comp (Subgroup.center ↥Q).subtype))
      (fun z hz k hk => hfp z hz k hk)
  -- Step 4: the centre has order `q`
  have hexp : ∀ z ∈ Subgroup.center ↥Q, z ^ q = 1 :=
    pow_eq_one_of_mem_center_of_center_eq_commutator hq hQp hZ hPhi
  have hexpC : ∀ z : ↥(Subgroup.center ↥Q), z ^ q = 1 := fun z =>
    Subtype.ext (by simpa [Subgroup.coe_pow] using hexp z z.2)
  have hntC : Nontrivial ↥(Subgroup.center ↥Q) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (center_ne_bot_of_center_eq_commutator hZ hQnab)
  have hcardC : Nat.card ↥(Subgroup.center ↥Q) = q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Subgroup.center ↥Q))
    have hgen : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
    have hcardg : Nat.card ↥(Subgroup.center ↥Q) = orderOf g := by
      rw [← Subgroup.card_top (G := ↥(Subgroup.center ↥Q)), ← hgen, Nat.card_zpowers]
    have hdiv : orderOf g ∣ q := orderOf_dvd_iff_pow_eq_one.mpr (hexpC g)
    have hne1 : orderOf g ≠ 1 := by
      intro h1
      have hg1 : g = 1 := orderOf_eq_one_iff.mp h1
      have htopbot : (⊤ : Subgroup ↥(Subgroup.center ↥Q)) = ⊥ := by
        rw [← hgen, hg1, Subgroup.zpowers_one_eq_bot]
      rw [Subgroup.eq_bot_iff_forall] at htopbot
      obtain ⟨x, y, hxy⟩ := hntC
      exact hxy (by rw [htopbot x (Subgroup.mem_top x), htopbot y (Subgroup.mem_top y)])
    rw [hcardg]
    rcases hq.eq_one_or_self_of_dvd (orderOf g) hdiv with h | h
    · exact absurd h hne1
    · exact h
  -- Step 5: `q` is odd
  have hcardCQ : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A)) = q := by
    rw [hCQ, Subgroup.card_map_of_injective Q.subtype_injective, hcardC]
  have hoddq : Odd q := by
    rw [← hcardCQ]
    exact hodd
  -- Step 6: `Q` is extraspecial
  have hcenterIn : Work.PGroup.centerIn (⊤ : Subgroup ↥Q) = Subgroup.center ↥Q :=
    centerIn_top_eq_center ↥Q
  have hfrattiniIn : Work.PGroup.frattiniIn (⊤ : Subgroup ↥Q) = frattini ↥Q :=
    frattiniIn_top_eq_frattini ↥Q
  have hQp' : IsPGroup q (⊤ : Subgroup ↥Q) :=
    isPGroup_iff_pow_pow_eq_one.mpr fun z =>
      let ⟨n, hn⟩ := hQp (z : ↥Q)
      ⟨n, Subtype.ext hn⟩
  have hnab : ¬ IsMulCommutative (⊤ : Subgroup ↥Q) := fun h =>
    hQnab (isMulCommutative_iff.mpr fun x y : ↥Q =>
      Subtype.ext_iff.mp (isMulCommutative_iff.mp h ⟨x, trivial⟩ ⟨y, trivial⟩))
  have hEA : Work.PGroup.IsElementaryAbelian q (Work.PGroup.centerIn (⊤ : Subgroup ↥Q)) := by
    rw [hcenterIn]
    exact ⟨inferInstance, fun x => hexpC x⟩
  have hspecial : Work.PGroup.IsSpecial q (⊤ : Subgroup ↥Q) := by
    refine Or.inr ⟨hQp', hnab, ?_, ?_, hEA⟩
    · rw [hcenterIn, hZ]
    · rw [hcenterIn, hfrattiniIn]
      refine le_antisymm ?_ hPhi
      rw [hZ, ← hfrattiniIn]
      exact Work.PGroup.commutator_le_frattiniIn hq (⊤ : Subgroup ↥Q) hQp'
  have hcardCI : Nat.card (Work.PGroup.centerIn (⊤ : Subgroup ↥Q)) = q := by
    rw [hcenterIn]; exact hcardC
  have hE : Work.PGroup.IsExtraspecial q (⊤ : Subgroup ↥Q) := ⟨hnab, hspecial, hcardCI⟩
  obtain ⟨m, hm1, hm⟩ := Work.PGroup.card_extraspecial hq (⊤ : Subgroup ↥Q) hE
  rw [Subgroup.card_top] at hm
  exact ⟨hoddq, m, hm1, hm, hE⟩

end Work.NormalComplement.AppVII
