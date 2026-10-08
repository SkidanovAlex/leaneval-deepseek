import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.card_T_eq_pow
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.higman_lemma7_psi
import Submission.Work.Higman.higman_lemma7_phi2
import Submission.Work.Higman.MSA.basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]


/-- The abstract counting lemma behind `higman_lemma7_layer`: in a finite abelian group `A` of
exponent dividing `2 ^ e` with `|A| = |A[2]| ^ e` (so the `2`-torsion grows uniformly), the
`2 ^ k`-th powers are exactly the elements killed by `2 ^ (e - k)`. -/
theorem pow_range_eq_torsion_self {A : Type} [CommGroup A] [Finite A] {e : ℕ}
    (hexp : ∀ a : A, a ^ 2 ^ e = 1)
    (hT : ∀ j ≤ e, Nat.card {x : A | x ^ 2 ^ j = 1} = (Nat.card {x : A | x ^ 2 = 1}) ^ j)
    (hA : Nat.card A = (Nat.card {x : A | x ^ 2 = 1}) ^ e) :
    ∀ k ≤ e, ∀ y : A, (∃ x : A, x ^ 2 ^ k = y) ↔ y ^ 2 ^ (e - k) = 1 := by
  intro k hk y
  set N : ℕ := Nat.card {x : A | x ^ 2 = 1} with hN
  haveI : Nonempty {x : A | x ^ 2 = 1} := ⟨⟨1, by simp⟩⟩
  have hNpos : 0 < N := by rw [hN]; exact Nat.card_pos
  let p : A →* A :=
    { toFun := fun x => x ^ 2 ^ k
      map_one' := one_pow _
      map_mul' := fun x y => (Commute.all x y).mul_pow (2 ^ k) }
  have hp : ∀ x : A, p x = x ^ 2 ^ k := fun x => rfl
  have hker : Nat.card ↥p.ker = N ^ k := by
    have h1 : p.ker = omega (A := A) k := by
      ext x
      rw [MonoidHom.mem_ker, mem_omega]
      exact ⟨fun h => by rw [← hp x]; exact h, fun h => by rw [hp]; exact h⟩
    have h2 : Nat.card ↥(omega (A := A) k) = Nat.card {x : A | x ^ 2 ^ k = 1} := rfl
    rw [h1, h2, hN]
    exact hT k hk
  have hrange_le : p.range ≤ omega (A := A) (e - k) := by
    rintro z ⟨x, rfl⟩
    rw [mem_omega]
    show (x ^ 2 ^ k) ^ 2 ^ (e - k) = 1
    rw [← pow_mul, Nat.mul_comm (2 ^ k) (2 ^ (e - k)), ← pow_add, Nat.sub_add_cancel hk]
    exact hexp x
  have hrange_card : Nat.card ↥p.range = N ^ (e - k) := by
    have hcm := card_ker_mul_card_range p
    rw [hker, hA] at hcm
    have heq : N ^ e = N ^ k * N ^ (e - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hNpos k) (by rw [hcm]; exact heq)
  have hcard_omega : Nat.card ↥(omega (A := A) (e - k)) = N ^ (e - k) := by
    have h2 : Nat.card ↥(omega (A := A) (e - k)) = Nat.card {x : A | x ^ 2 ^ (e - k) = 1} := rfl
    rw [h2, hN]
    exact hT (e - k) (Nat.sub_le e k)
  have hrange_eq : p.range = omega (A := A) (e - k) :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hcard_omega, hrange_card])
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_omega.mp (hrange_le ⟨x, rfl⟩)
  · intro hy
    have hy' : y ∈ p.range := by rw [hrange_eq, mem_omega]; exact hy
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy'
    exact ⟨x, hx⟩

/-- The two-torsion of `A` has the same order as `A ⊓ Ω₁(P)`. -/
theorem card_two_torsion_eq_inf_omega1 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card {x : ↥A | x ^ 2 = 1} = Nat.card ↥(A ⊓ Work.Higman.omega1 P) := by
  letI : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun x y => Subtype.ext (hab x.1 x.2 y.1 y.2) }
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, ?_⟩⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  · show x.1.1 ∈ Work.Higman.omega1 P
    rw [h.mem_omega1]
    simpa using congrArg (Subtype.val : ↥A → P) x.2
  · refine Subtype.ext ?_
    show (y : P) ^ 2 = (1 : P)
    exact h.mem_omega1.mp (Subgroup.mem_inf.mp y.2).2

/-- In a homocyclic abelian `2`-group `A` of exponent `2 ^ e` (with `|A| = |A ⊓ Ω₁| ^ e`),
the `2 ^ k`-th power subgroup `A ^ (2 ^ k)` is exactly the set of elements of `A` whose
`2 ^ (e-k)`-th power is trivial. -/
theorem higman_lemma7_layer_self {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e : ℕ} (he : 1 ≤ e)
    (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hcard : Nat.card ↥A = (Nat.card ↥(A ⊓ Work.Higman.omega1 P)) ^ e) :
    ∀ k ≤ e, ∀ y ∈ A, y ∈ Work.Higman.powSub A (2 ^ k) ↔ y ^ 2 ^ (e - k) = 1 := by
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun x y => Subtype.ext (hab x.1 x.2 y.1 y.2) }
  have hexp' : ∀ a : ↥A, a ^ 2 ^ e = 1 := fun a => Subtype.ext (by simpa using h1 a.1 a.2)
  have hcard' : Nat.card ↥A = (Nat.card {x : ↥A | x ^ 2 = 1}) ^ e := by
    rw [card_two_torsion_eq_inf_omega1 h hab]
    exact hcard
  have hT : ∀ j ≤ e,
      Nat.card {x : ↥A | x ^ 2 ^ j = 1} = (Nat.card {x : ↥A | x ^ 2 = 1}) ^ j :=
    card_T_eq_pow (A := ↥A) hexp' hcard'
  have hkey : ∀ k ≤ e, ∀ y : ↥A,
      (∃ x : ↥A, x ^ 2 ^ k = y) ↔ y ^ 2 ^ (e - k) = 1 :=
    pow_range_eq_torsion_self (A := ↥A) hexp' hT hcard'
  intro k hk y hy
  have hk' := hkey k hk (⟨y, hy⟩ : ↥A)
  rw [mem_powSub_iff hab]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : (⟨x, hx⟩ : ↥A) ^ 2 ^ k = (⟨y, hy⟩ : ↥A) := Subtype.ext (by simpa using hxy)
    have h := hk'.mp ⟨⟨x, hx⟩, hxy'⟩
    have := congrArg (Subtype.val : ↥A → P) h
    simpa using this
  · intro hy1
    have hy1' : (⟨y, hy⟩ : ↥A) ^ 2 ^ (e - k) = 1 := Subtype.ext (by simpa using hy1)
    obtain ⟨x, hx⟩ := hk'.mpr hy1'
    exact ⟨x.1, x.2, by
      have := congrArg (Subtype.val : ↥A → P) hx
      simpa using this⟩

/-- Restriction of a `MulAut` of `P` to a subgroup that it preserves. -/
def subgroupMulAut (φ : MulAut P) (T : Subgroup P) (hT : T.map φ.toMonoidHom = T) :
    MulAut ↥T where
  toFun t := ⟨φ (t : P), by
    have h := Subgroup.mem_map_of_mem φ.toMonoidHom t.2
    rwa [hT] at h⟩
  invFun t := ⟨φ.symm (t : P), symm_mem_of_map_eq φ hT t.2⟩
  left_inv t := Subtype.ext (by simp)
  right_inv t := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

@[simp] theorem subgroupMulAut_apply (φ : MulAut P) (T : Subgroup P)
    (hT : T.map φ.toMonoidHom = T) (t : ↥T) :
    ((subgroupMulAut φ T hT t : ↥T) : P) = φ (t : P) := rfl

theorem subgroupMulAut_pow_apply (φ : MulAut P) (T : Subgroup P)
    (hT : T.map φ.toMonoidHom = T) (k : ℕ) (t : ↥T) :
    (((subgroupMulAut φ T hT) ^ k) t : P) = (φ ^ k) (t : P) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply]
      show φ ((((subgroupMulAut φ T hT) ^ k) t : ↥T) : P) = (φ ^ (k + 1)) (t : P)
      rw [ih, ← MulAut.mul_apply, ← pow_succ']

/-- If `A` is an abelian normal subgroup of a group `G` and `A ≤ C`, then for every `c ∈ C`
the map `a ↦ ⁅a, c⁆` is multiplicative on `A`. -/
theorem mul_of_abel_normal_self {G : Type} [Group G] {A C : Subgroup G}
    (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) {c : G} (hc : c ∈ C) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  haveI : A.Normal := hAn
  have hac : ⁅a, c⁆ ∈ A :=
    Subgroup.commutator_le_left A C (Subgroup.commutator_mem_commutator ha hc)
  have hbc : ⁅b, c⁆ ∈ A :=
    Subgroup.commutator_le_left A C (Subgroup.commutator_mem_commutator hb hc)
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    rw [hAb a ha ⁅b, c⁆ hbc, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1, hAb ⁅b, c⁆ hbc ⁅a, c⁆ hac]

/-- The commutator of a square (Mathlib convention `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`):
`⁅x ^ 2, c⁆ = ⁅x, ⁅x, c⁆⁆ * ⁅x, c⁆ ^ 2`. -/
theorem commutatorElement_sq_self {G : Type} [Group G] (x c : G) :
    ⁅x ^ 2, c⁆ = ⁅x, ⁅x, c⁆⁆ * ⁅x, c⁆ ^ 2 := by
  simp only [commutatorElement_def, pow_two]
  group

/-- If `A = Φ(C)` is a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group with
`C' ≤ A²` and `C' = A ^ (2 ^ s)`, then `[A,C]` and `[C',C]` both lie in `(C')²`. -/
theorem higman_lemma7_comm_le_self {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A) (hCn : C.Normal)
    (hAC : A ≤ C) (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A)
    (hCd : ⁅C, C⁆ ≤ Work.Higman.powSub A 2)
    {e s : ℕ} (hs : 1 ≤ s) (hse : s ≤ e - 1) (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hDs : ⁅C, C⁆ = Work.Higman.powSub A (2 ^ s)) :
    ⁅A, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 ∧
      ⁅⁅C, C⁆, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 := by
  haveI hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hDA : ⁅C, C⁆ ≤ A := by rw [← hPhi]; exact le_sup_right
  have step2 : ∀ d ∈ ⁅C, C⁆, ∀ c ∈ C, ⁅d, c⁆ ∈ Work.Higman.powSub ⁅C, C⁆ 2 := by
    intro d hd c hc
    obtain ⟨a, ha, haeq⟩ := (Work.Higman.mem_powSub_iff hAb).mp (hDs ▸ hd)
    have hac : ⁅a, c⁆ ∈ A :=
      Subgroup.commutator_le_left A C (Subgroup.commutator_mem_commutator ha hc)
    have hacD : ⁅a, c⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (hAC ha) hc
    have hcomm : Commute a ⁅a, c⁆ := hAb a ha ⁅a, c⁆ hac
    rw [← haeq, ← Commute.commutatorElement_pow_left hcomm (2 ^ s)]
    have hp : (2 : ℕ) ^ s = 2 ^ (s - 1) * 2 := by
      conv_lhs => rw [show s = (s - 1) + 1 by omega]
      rw [pow_succ]
    rw [hp, pow_mul]
    exact Work.Higman.pow_mem_powSub (Subgroup.pow_mem ⁅C, C⁆ hacD (2 ^ (s - 1)))
  have step2' : ∀ x ∈ C, ∀ d ∈ ⁅C, C⁆, ⁅x, d⁆ ∈ Work.Higman.powSub ⁅C, C⁆ 2 := by
    intro x hx d hd
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (step2 d hd x hx)
  let T : Subgroup P :=
    { carrier := {g : P | g ∈ A ∧ ∀ c ∈ C, ⁅g, c⁆ ∈ Work.Higman.powSub ⁅C, C⁆ 2}
      one_mem' := ⟨A.one_mem, by
        intro c hc
        rw [commutatorElement_one_left]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro g g' ⟨hgA, hg⟩ ⟨hgA', hg'⟩
        refine ⟨A.mul_mem hgA hgA', fun c hc => ?_⟩
        rw [mul_of_abel_normal_self hAn hAb hgA hgA' hc]
        exact Subgroup.mul_mem _ (hg c hc) (hg' c hc)
      inv_mem' := by
        rintro g ⟨hgA, hg⟩
        refine ⟨A.inv_mem hgA, fun c hc => ?_⟩
        have hmul := mul_of_abel_normal_self hAn hAb hgA (A.inv_mem hgA) hc
        have hone : ⁅g * g⁻¹, c⁆ = 1 := by rw [mul_inv_cancel, commutatorElement_one_left]
        rw [hone] at hmul
        have hinv : ⁅g⁻¹, c⁆ = ⁅g, c⁆⁻¹ := eq_inv_of_mul_eq_one_right hmul.symm
        rw [hinv]
        exact Subgroup.inv_mem _ (hg c hc) }
  have hC2A : Work.Higman.powSub C 2 ≤ A := by rw [← hPhi]; exact le_sup_left
  have hTpow : Work.Higman.powSub C 2 ≤ T := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    refine ⟨hC2A (Work.Higman.pow_mem_powSub hx), fun c hc => ?_⟩
    rw [commutatorElement_sq_self]
    have hxc : ⁅x, c⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hc
    exact Subgroup.mul_mem _ (step2' x hx ⁅x, c⁆ hxc)
      (Work.Higman.pow_mem_powSub hxc)
  have hTD : ⁅C, C⁆ ≤ T := fun d hd => ⟨hDA hd, fun c hc => step2 d hd c hc⟩
  have hTA : A ≤ T := by
    rw [← hPhi]
    exact sup_le hTpow hTD
  constructor
  · rw [Subgroup.commutator_le]
    exact fun g hg c hc => (hTA hg).2 c hc
  · rw [Subgroup.commutator_le]
    exact fun d hd c hc => step2 d hd c hc

namespace MSA

/-- **Higman 1963, Lemma 7** (own copy for the Lemma-9 development; the existing
`Submission/Work/Higman/higman_lemma7.lean` states the same thing and is imported by
`maximal_abelian_invariant_ge_phi.lean`, so once this is proved switch that import to this file).

`A` is a normal abelian `ξ`-subgroup of a Suzuki 2-group `P`, `C ⊵ A` is normal and `ξ`-invariant
with `A < C` and `C/A` a minimal normal `ξ`-section (`hcover`).  If `Φ(C) = A` (i.e.
`powSub C 2 ⊔ ⁅C,C⁆ = A`) and `C' = ⁅C,C⁆ ≤ A²`, then `C` is abelian.

PROOF (verified outline; see `Submission/Work/Higman/MSA_NOTES.md` §5).  Put `V := C/A` and
`W := A/A²`.  Assume `C' ≠ 1`; then `C' = powSub A (2^j)` (`homogeneous_structure`) with `j ≥ 1`
(because `C' ⊆ A²`), since `C'` is `ξ`-invariant and `≤ A`.

1. `q : V → W`, `q(cA) = c²A²`, is well defined (unipotence: `(ca)² ≡ c² mod A²`), additive
   (`(cc')² = c²c'²[c',c]` and `[c',c] ∈ C' ⊆ A²`), `ξ`-equivariant, injective (`K := {c ∈ C |
   c² ∈ A²}` is a subgroup by `[c',c] ∈ A²`, normal, `ξ`-invariant, `A ≤ K ≤ C`; `hcover` gives
   `K = A` unless `K = C`, which forces `A = C²C' ⊆ C²A²`, hence `A = A²` and `A = ⊥`; then
   `Φ(C) = A = ⊥` gives `C = ⊥ = A`, contradiction) and surjective (`A = C²C' ⊆ C²A²`).  So `q`
   is a bijection; since `q(V) ∖ 0 ≠ ∅` is `ξ`-stable and `ξ` is transitive on `W ∖ 0`
   (`Work.Higman.xi_trans_quot_sq`), `ξ` is transitive on `V ∖ 0` (a `ξ`-invariant non-empty
   subset of `W∖0` is all of `W∖0`).

2. The commutator pairing `γ : V × V → T := C'/([A,C]·[C',C])`, `γ(x,y) = [x,y]`, is well
   defined (`[ca,c'] = [c,c']^a[a,c']` and `[c,c']^a = [c,c']` because `C' ⊆ A` is abelian;
   `[a,c'] ∈ [A,C] ⊆ T`), biadditive (`[cc',c''] = [c,c''][[c,c''],c'][c',c'']` and
   `[[c,c''],c'] ∈ [C',C] ⊆ T`), alternating, `ξ`-equivariant and onto (its image generates
   `C' = [C,C]`).
   `T` is a *quotient of the `ξ`-module* `W` (use `C' = powSub A (2^j)`,
   `homogeneous_structure`'s power-map identification `W ≅ C'/powSub C' 2`, and
   `Work.Higman.MSA.eq_one_of_alt_of_target_iso`): since `W` is irreducible
   (`xi_invariant_eq_powSub_two_or_self`) either `T = 1` or `T ≃* W` compatibly with `ξ`, and in
   the second case the transported pairing is trivial by `eq_one_of_alt_of_target_iso`.  So
   `γ ≡ 1` and `C' ⊆ [A,C]·[C',C]`.  As `[C',C] = [powSub A (2^j), C] = ([A,C])^(2^j) ⊆ [A,C]`
   (for fixed `c`, `a ↦ [a,c]` is a homomorphism `A → A`), we get `C' = [A,C]`.

3. For fixed `c ∈ C` the map `a ↦ [a,c]` is a homomorphism `A → C'`, so `δ(a,c̄) := [a,c]` gives
   a biadditive map `A × V → C'`, additive in the second variable modulo
   `[C',C] = ([A,C])^(2^j) = powSub A (2^(2j))`, with `δ(a²,c) = [a,c]² ∈ (C')² =
   powSub A (2^(j+1))`.  Hence `δ` descends to a biadditive `ξ`-equivariant surjection
   `δ̄ : (A/A²) × V → C'/(powSub A (2^(2j))·powSub A (2^(j+1))) = powSub A (2^j)/powSub A (2^(j+1))`.
   Identifying `V ≅ A/A²` (via `q`) and `powSub A (2^j)/powSub A (2^(j+1)) ≅ A/A²` (power map),
   `δ̄` becomes a biadditive *alternating* `ξ`-equivariant surjection `W × W → W`: alternation is
   checked on the diagonal — if `q(c̄) = ā`, i.e. `a = c²d` with `d ∈ A²`, then
   `[a,c] = [c²,c]·[d,c] = [d,c] ∈ [A²,C] = ([A,C])² = powSub A (2^(2j)) ⊆ powSub A (2^(j+1))`.
   By `eq_one_of_alt_of_target_iso` (or `equivariant_bihom_trivial`) applied to `W`, this map is
   trivial, so `powSub A (2^j) = powSub A (2^(j+1))`, contradicting the cardinality formula of
   `homogeneous_structure` (`|powSub A (2^i)| = q ^ (e - i)` with `q = |A ⊓ Ω₁| ≥ 2`, as `A ≠ ⊥`
   is a subgroup of a `2`-group).

Hence `C' = 1`: `C` is abelian. -/
theorem higman_lemma7_msa {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A)
    (hCd : ⁅C, C⁆ ≤ Work.Higman.powSub A 2) :
    ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
  classical
  suffices hDbot : ⁅C, C⁆ = ⊥ by
    intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hDbot] at hmem
    exact (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hmem)).eq
  by_contra hDne
  have hDleA : ⁅C, C⁆ ≤ A := by rw [← hPhi]; exact le_sup_right
  have hDvN : (⁅C, C⁆).Normal := Subgroup.commutator_normal C C
  have hAne : A ≠ ⊥ := fun hbot => hDne (le_bot_iff.mp (hDleA.trans (le_of_eq hbot)))
  -- exponent data for `A`
  obtain ⟨e, he1, he2, hcard⟩ := higman_lemma1 h hA.abelian hA.map_eq
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he0 | hpos
    · exfalso
      have hbot : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro a ha
        have hh := he1 a ha
        simpa [he0] using hh
      exact hAne hbot
    · exact hpos
  -- the group `W = A ∩ Ω₁`
  set W : Subgroup P := A ⊓ Work.Higman.omega1 P with hWdef
  have hWle : W ≤ A := inf_le_left
  have hWmem : ∀ x ∈ A, x ^ 2 = 1 ↔ x ∈ W := by
    intro x hx
    rw [hWdef, Subgroup.mem_inf]
    exact ⟨fun h2 => ⟨hx, h.mem_omega1.mpr h2⟩, fun hh => h.mem_omega1.mp hh.2⟩
  obtain ⟨hcard_pow, hker⟩ := powSub_chain_card W hA.abelian hWle hWmem e he1 hcard
  have hWinv : W.map (h.xi : MulAut P).toMonoidHom = W := by
    rw [hWdef, Subgroup.map_inf _ _ _ (h.xi : MulAut P).injective, hA.map_eq, map_xi_omega1 h]
  have hirr : ∀ T : Subgroup P, T ≤ W → T.map (h.xi : MulAut P).toMonoidHom = T →
      T = ⊥ ∨ T = W := by
    intro T hT hTinv
    have hT' : T ≤ A ⊓ Work.Higman.omega1 P := by rw [← hWdef]; exact hT
    have hgoal := invariant_subgroup_inf_omega1 h A hT' hTinv
    rwa [hWdef]
  have hDinv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator C C (h.xi : MulAut P).toMonoidHom, hCinv]
  obtain ⟨s, hDs⟩ :=
    invariant_subgroup_eq_powSub (φ := h.xi) (W := W) hWinv e A hA.abelian hWmem hirr he1 hcard
      hker ⁅C, C⁆ hDleA hDinv
  have hse : s ≤ e - 1 := by
    by_contra hcon
    push_neg at hcon
    have hes : e ≤ s := by omega
    exact hDne (by rw [hDs, powSub_eq_bot_of_exp hA.abelian hes he1])
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hpos
    · exfalso
      have hAD : A = ⁅C, C⁆ := by rw [hDs, hs0, pow_zero, powSub_one_eq]
      have hAle : A ≤ Work.Higman.powSub A 2 := hAD.symm ▸ hCd
      have hA2 : A = Work.Higman.powSub A 2 :=
        le_antisymm hAle (powSub_le (by norm_num))
      have hpow : ∀ k : ℕ, Work.Higman.powSub A (2 ^ k) = A := by
        intro k
        induction k with
        | zero => rw [pow_zero, powSub_one_eq]
        | succ k ih =>
            rw [pow_succ, ← powSub_powSub hA.abelian (2 ^ k) 2, ih]
            exact hA2.symm
      exact hAne (by rw [← hpow e, powSub_eq_bot_of_exp hA.abelian le_rfl he1])
    · exact hpos
  -- ## the four auxiliary inputs (delegated)
  have hkeyk : ∀ k ≤ e, ∀ y ∈ A, y ∈ Work.Higman.powSub A (2 ^ k) ↔ y ^ 2 ^ (e - k) = 1 :=
    higman_lemma7_layer_self h hA.abelian he he1 hcard
  have hkey : ∀ y ∈ A, y ∈ Work.Higman.powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1 :=
    fun y hy => hkeyk 1 he y hy
  have hcomm : ⁅A, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 ∧
      ⁅⁅C, C⁆, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 :=
    higman_lemma7_comm_le_self h hA hCn hAC hPhi hCd hs hse he1 hDs
  obtain ⟨hcommAC, hcommDC⟩ := hcomm
  have hphi2 : (∀ x ∈ C, ∀ y ∈ C, (x * y) ^ 2 ^ e = x ^ 2 ^ e * y ^ 2 ^ e) ∧
      (∀ x ∈ C, x ^ 2 ^ e ∈ A ⊓ Work.Higman.omega1 P) ∧
      (∀ w ∈ A ⊓ Work.Higman.omega1 P, ∃ x ∈ C, x ^ 2 ^ e = w) ∧
      (∀ x ∈ C, x ^ 2 ^ e = 1 ↔ x ∈ A) ∧
      (∀ x ∈ C, (h.xi x) ^ 2 ^ e = h.xi (x ^ 2 ^ e)) :=
    higman_lemma7_phi2 h hA hCn hCinv hAC hCA hcover hPhi hCd hAne he he1 hkey hker
  obtain ⟨hphi2_mul, hphi2_mem, hphi2_surj, hphi2_ker, hphi2_xi⟩ := hphi2
  have hpsi : (∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) ∈ A ⊓ Work.Higman.omega1 P) ∧
      (∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆,
        (u * v) ^ 2 ^ (e - 1 - s) = u ^ 2 ^ (e - 1 - s) * v ^ 2 ^ (e - 1 - s)) ∧
      (∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) = 1 ↔ v ∈ Work.Higman.powSub ⁅C, C⁆ 2) ∧
      (∀ v ∈ ⁅C, C⁆, h.xi (v ^ 2 ^ (e - 1 - s)) = (h.xi v) ^ 2 ^ (e - 1 - s)) :=
    higman_lemma7_psi h hA hse hkeyk hker hDs
  obtain ⟨hpsi_mem, hpsi_mul, hpsi_ker, hpsi_xi⟩ := hpsi
  -- ## `W` is elementary abelian, and `ξ` acts transitively on `W \ {1}`
  letI hWcomm : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with
      mul_comm := fun u v => Subtype.ext
        (h.omega1_comm (Subgroup.mem_inf.mp (show (u:P) ∈ A ⊓ Work.Higman.omega1 P from u.2)).2
                       (Subgroup.mem_inf.mp (show (v:P) ∈ A ⊓ Work.Higman.omega1 P from v.2)).2) }
  have hWtwo : ∀ a : ↥W, a * a = 1 := by
    intro a
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two,
      h.mem_omega1.mp (Subgroup.mem_inf.mp (show (a:P) ∈ A ⊓ Work.Higman.omega1 P from a.2)).2]
  let ξW : MulAut ↥W := subgroupMulAut (h.xi : MulAut P) W hWinv
  have hξW_pow : ∀ (k : ℕ) (w : ↥W), (((ξW ^ k) w : ↥W) : P) = (h.xi ^ k) (w : P) :=
    subgroupMulAut_pow_apply (h.xi : MulAut P) W hWinv
  have htransW : ∀ a b : ↥W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b := by
    intro a b ha hb
    have ha2 : orderOf (a:P) = 2 := by
      have h2 : (a:P) ^ 2 = 1 := by
        have hh := congrArg (fun t : ↥W => (t:P)) (hWtwo a)
        simpa [pow_two] using hh
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) (fun hc => ha (Subtype.ext hc))
      · exact h1
    have hb2 : orderOf (b:P) = 2 := by
      have h2 : (b:P) ^ 2 = 1 := by
        have hh := congrArg (fun t : ↥W => (t:P)) (hWtwo b)
        simpa [pow_two] using hh
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) (fun hc => hb (Subtype.ext hc))
      · exact h1
    obtain ⟨k, hk⟩ := h.trans (a:P) (b:P) ha2 hb2
    exact ⟨k, Subtype.ext (by rw [hξW_pow]; exact hk)⟩
  -- ## the map `Φ₂ : C → W`, `x ↦ x ^ 2 ^ e`
  let Φ2 : ↥C →* ↥W :=
    { toFun := fun x => ⟨(x : P) ^ 2 ^ e, hphi2_mem (x : P) x.2⟩
      map_one' := Subtype.ext (by show ((1:↥C):P) ^ 2 ^ e = 1; simp)
      map_mul' := fun x y => Subtype.ext (by
        show ((x * y : ↥C) : P) ^ 2 ^ e = ((x:P) ^ 2 ^ e) * ((y:P) ^ 2 ^ e)
        rw [Subgroup.coe_mul]
        exact hphi2_mul (x:P) x.2 (y:P) y.2) }
  have hkerΦ2 : ∀ x : ↥C, Φ2 x = 1 ↔ (x : P) ∈ A := by
    intro x
    have h4 := hphi2_ker (x:P) x.2
    constructor
    · intro hx
      have h := congrArg (fun t : ↥W => (t:P)) hx
      simp only [Subgroup.coe_one] at h
      exact h4.mp h
    · intro hx
      refine Subtype.ext ?_
      show (x:P) ^ 2 ^ e = 1
      exact h4.mpr hx
  have hsurjΦ2 : ∀ w : ↥W, ∃ x : ↥C, Φ2 x = w := by
    intro w
    obtain ⟨x, hxC, hxw⟩ :=
      hphi2_surj (w:P) (show (w:P) ∈ A ⊓ Work.Higman.omega1 P from w.2)
    exact ⟨⟨x, hxC⟩, Subtype.ext hxw⟩
  let lift : ↥W → ↥C := fun w => Classical.choose (hsurjΦ2 w)
  have lift_spec : ∀ w : ↥W, Φ2 (lift w) = w := fun w => Classical.choose_spec (hsurjΦ2 w)
  have lift_val : ∀ w : ↥W, ((lift w : ↥C) : P) ^ 2 ^ e = (w:P) :=
    fun w => congrArg (fun t : ↥W => (t:P)) (lift_spec w)
  let Ψ : ↥(⁅C, C⁆) →* ↥W :=
    { toFun := fun v => ⟨(v : P) ^ 2 ^ (e - 1 - s), hpsi_mem (v : P) v.2⟩
      map_one' := Subtype.ext (by show ((1:↥(⁅C,C⁆)):P) ^ 2 ^ (e-1-s) = 1; simp)
      map_mul' := fun u v => Subtype.ext (by
        show ((u * v : ↥(⁅C, C⁆)) : P) ^ 2 ^ (e - 1 - s)
          = ((u:P) ^ 2 ^ (e - 1 - s)) * ((v:P) ^ 2 ^ (e - 1 - s))
        rw [Subgroup.coe_mul]
        exact hpsi_mul (u:P) u.2 (v:P) v.2) }
  have hΨker : ∀ v : ↥(⁅C, C⁆), Ψ v = 1 ↔ (v : P) ∈ Work.Higman.powSub ⁅C, C⁆ 2 := by
    intro v
    have h := hpsi_ker (v:P) v.2
    constructor
    · intro hv
      have hh := congrArg (fun t : ↥W => (t:P)) hv
      simp only [Subgroup.coe_one] at hh
      exact h.mp hh
    · intro hv
      refine Subtype.ext ?_
      show (v:P) ^ 2 ^ (e - 1 - s) = 1
      exact h.mpr hv
  have hPsi_xi : ∀ v : ↥(⁅C, C⁆),
      Ψ ⟨h.xi (v:P), by
          have hh := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom v.2
          rwa [Subgroup.map_commutator C C (h.xi : MulAut P).toMonoidHom, hCinv] at hh⟩
        = ξW (Ψ v) := by
    intro v
    refine Subtype.ext ?_
    show (h.xi (v:P)) ^ 2 ^ (e - 1 - s) = h.xi ((v:P) ^ 2 ^ (e - 1 - s))
    exact (hpsi_xi (v:P) v.2).symm
  have hΨconj : ∀ (g : P) (hg : g ∈ C) (d : ↥(⁅C, C⁆)),
      Ψ ⟨g * (d:P) * g⁻¹, hDvN.conj_mem (d:P) d.2 g⟩ = Ψ d := by
    intro g hg d
    have hcd : ⁅g, (d:P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hg (hAC (hDleA d.2))
    have helem : (⟨g * (d:P) * g⁻¹, hDvN.conj_mem (d:P) d.2 g⟩ : ↥(⁅C, C⁆))
        = ⟨⁅g, (d:P)⁆, hcd⟩ * ⟨(d:P), d.2⟩ := by
      refine Subtype.ext ?_
      show g * (d:P) * g⁻¹ = ⁅g, (d:P)⁆ * (d:P)
      rw [commutatorElement_def]; group
    rw [helem, map_mul]
    have hmem_dg : ⁅(d:P), g⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (hAC (hDleA d.2)) hg
    have hone : Ψ ⟨⁅g, (d:P)⁆, hcd⟩ = 1 := by
      have hdg : Ψ (⟨⁅(d:P), g⁆, hmem_dg⟩ : ↥(⁅C, C⁆)) = 1 :=
        (hΨker _).mpr (hcommDC (Subgroup.commutator_mem_commutator d.2 hg))
      have heq2 : (⟨⁅g, (d:P)⁆, hcd⟩ : ↥(⁅C, C⁆))
          = (⟨⁅(d:P), g⁆, hmem_dg⟩ : ↥(⁅C, C⁆))⁻¹ := by
        refine Subtype.ext ?_
        show ⁅g, (d:P)⁆ = ⁅(d:P), g⁆⁻¹
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [heq2, map_inv, hdg, inv_one]
    rw [hone, one_mul]
  have hwd1 : ∀ (x x' z : ↥C), Φ2 x = Φ2 x' →
      Ψ ⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ =
      Ψ ⟨⁅(x':P), (z:P)⁆, Subgroup.commutator_mem_commutator x'.2 z.2⟩ := by
    intro x x' z hxx'
    have hmem : ((x:P) * (x':P)⁻¹) ∈ A := by
      have hk : Φ2 (x * x'⁻¹) = 1 := by rw [map_mul, map_inv, hxx', mul_inv_cancel]
      exact (hkerΦ2 (x * x'⁻¹)).mp hk
    have haC : ((x:P) * (x':P)⁻¹) ∈ C := hAC hmem
    have hxD : ⁅(x':P), (z:P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator x'.2 z.2
    have haD : ⁅((x:P) * (x':P)⁻¹), (z:P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator haC z.2
    have hconjD : ((x:P) * (x':P)⁻¹) * ⁅(x':P), (z:P)⁆ * ((x:P) * (x':P)⁻¹)⁻¹ ∈ ⁅C, C⁆ :=
      hDvN.conj_mem _ hxD ((x:P) * (x':P)⁻¹)
    have helem : (⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ : ↥(⁅C, C⁆))
        = ⟨((x:P) * (x':P)⁻¹) * ⁅(x':P), (z:P)⁆ * ((x:P) * (x':P)⁻¹)⁻¹, hconjD⟩
          * ⟨⁅((x:P) * (x':P)⁻¹), (z:P)⁆, haD⟩ := by
      refine Subtype.ext ?_
      show ⁅(x:P), (z:P)⁆
        = ((x:P) * (x':P)⁻¹) * ⁅(x':P), (z:P)⁆ * ((x:P) * (x':P)⁻¹)⁻¹
          * ⁅((x:P) * (x':P)⁻¹), (z:P)⁆
      conv_lhs => rw [show (x:P) = ((x:P) * (x':P)⁻¹) * (x':P) from by group]
      rw [commutatorElement_mul_left_eq_conj_mul]
    rw [helem, map_mul]
    rw [hΨconj ((x:P) * (x':P)⁻¹) haC ⟨⁅(x':P), (z:P)⁆, hxD⟩]
    have hone : Ψ ⟨⁅((x:P) * (x':P)⁻¹), (z:P)⁆, haD⟩ = 1 :=
      (hΨker _).mpr (hcommAC (Subgroup.commutator_mem_commutator hmem z.2))
    rw [hone, mul_one]
  have hwd2 : ∀ (x z z' : ↥C), Φ2 z = Φ2 z' →
      Ψ ⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ =
      Ψ ⟨⁅(x:P), (z':P)⁆, Subgroup.commutator_mem_commutator x.2 z'.2⟩ := by
    intro x z z' hzz'
    have hmem : ((z:P) * (z':P)⁻¹) ∈ A := by
      have hk : Φ2 (z * z'⁻¹) = 1 := by rw [map_mul, map_inv, hzz', mul_inv_cancel]
      exact (hkerΦ2 (z * z'⁻¹)).mp hk
    have hbC : ((z:P) * (z':P)⁻¹) ∈ C := hAC hmem
    have hxb : ⁅(x:P), ((z:P) * (z':P)⁻¹)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator x.2 hbC
    have hzD : ⁅(x:P), (z':P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator x.2 z'.2
    have hconjD : ((z:P) * (z':P)⁻¹) * ⁅(x:P), (z':P)⁆ * ((z:P) * (z':P)⁻¹)⁻¹ ∈ ⁅C, C⁆ :=
      hDvN.conj_mem _ hzD ((z:P) * (z':P)⁻¹)
    have helem : (⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ : ↥(⁅C, C⁆))
        = ⟨⁅(x:P), ((z:P) * (z':P)⁻¹)⁆, hxb⟩
          * ⟨((z:P) * (z':P)⁻¹) * ⁅(x:P), (z':P)⁆ * ((z:P) * (z':P)⁻¹)⁻¹, hconjD⟩ := by
      refine Subtype.ext ?_
      show ⁅(x:P), (z:P)⁆
        = ⁅(x:P), ((z:P) * (z':P)⁻¹)⁆
          * (((z:P) * (z':P)⁻¹) * ⁅(x:P), (z':P)⁆ * ((z:P) * (z':P)⁻¹)⁻¹)
      conv_lhs => rw [show (z:P) = ((z:P) * (z':P)⁻¹) * (z':P) from by group]
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    rw [helem, map_mul]
    rw [hΨconj ((z:P) * (z':P)⁻¹) hbC ⟨⁅(x:P), (z':P)⁆, hzD⟩]
    have hmemC : ⁅((z:P) * (z':P)⁻¹), (x:P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (hAC hmem) x.2
    have hACp : ⁅((z:P) * (z':P)⁻¹), (x:P)⁆ ∈ Work.Higman.powSub ⁅C, C⁆ 2 :=
      hcommAC (Subgroup.commutator_mem_commutator hmem x.2)
    have hone : Ψ ⟨⁅(x:P), ((z:P) * (z':P)⁻¹)⁆, hxb⟩ = 1 := by
      have heq2 : (⟨⁅(x:P), ((z:P) * (z':P)⁻¹)⁆, hxb⟩ : ↥(⁅C, C⁆))
          = (⟨⁅((z:P) * (z':P)⁻¹), (x:P)⁆, hmemC⟩ : ↥(⁅C, C⁆))⁻¹ := by
        refine Subtype.ext ?_
        show ⁅(x:P), ((z:P) * (z':P)⁻¹)⁆ = ⁅((z:P) * (z':P)⁻¹), (x:P)⁆⁻¹
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [heq2, map_inv,
        show Ψ (⟨⁅((z:P) * (z':P)⁻¹), (x:P)⁆, hmemC⟩ : ↥(⁅C, C⁆)) = 1 from
          (hΨker _).mpr hACp, inv_one]
    rw [hone, one_mul]
  let c : ↥W → ↥W → ↥W := fun w w' =>
    Ψ ⟨⁅((lift w : ↥C) : P), ((lift w' : ↥C) : P)⁆,
      Subgroup.commutator_mem_commutator (lift w).2 (lift w').2⟩
  have hc_apply : ∀ w w' : ↥W, c w w' = Ψ ⟨⁅((lift w : ↥C) : P), ((lift w' : ↥C) : P)⁆,
      Subgroup.commutator_mem_commutator (lift w).2 (lift w').2⟩ := fun _ _ => rfl
  have halt : ∀ a : ↥W, c a a = 1 := by
    intro a
    rw [hc_apply]
    have h1 : (⟨⁅((lift a : ↥C) : P), ((lift a : ↥C) : P)⁆,
        Subgroup.commutator_mem_commutator (lift a).2 (lift a).2⟩ : ↥(⁅C, C⁆)) = 1 := by
      refine Subtype.ext ?_
      show ⁅((lift a : ↥C) : P), ((lift a : ↥C) : P)⁆ = 1
      simp [commutatorElement_def]
    rw [h1, map_one]
  have hmul : ∀ a b d : ↥W, c (a * b) d = c a d * c b d := by
    intro a b d
    have hlift : Φ2 (lift (a * b)) = Φ2 (lift a * lift b) := by
      rw [map_mul, lift_spec, lift_spec, lift_spec]
    have h1 := hwd1 (lift (a * b)) (lift a * lift b) (lift d) hlift
    have hD_b : ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift b).2 (lift d).2
    have hD_a : ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift a).2 (lift d).2
    have hconj_ab : ((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
        * ((lift a : ↥C) : P)⁻¹ ∈ ⁅C, C⁆ := hDvN.conj_mem _ hD_b _
    rw [hc_apply, hc_apply, hc_apply, h1]
    have helem : (⟨⁅(((lift a : ↥C) * (lift b : ↥C) : ↥C) : P), ((lift d : ↥C) : P)⁆,
          Subgroup.commutator_mem_commutator (lift a * lift b).2 (lift d).2⟩ : ↥(⁅C, C⁆))
        = (⟨((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
              * ((lift a : ↥C) : P)⁻¹, hconj_ab⟩ : ↥(⁅C, C⁆))
          * (⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_a⟩ : ↥(⁅C, C⁆)) := by
      refine Subtype.ext ?_
      show ⁅(((lift a : ↥C) * (lift b : ↥C) : ↥C) : P), ((lift d : ↥C) : P)⁆
        = ((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
            * ((lift a : ↥C) : P)⁻¹
          * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
      rw [Subgroup.coe_mul, commutatorElement_mul_left_eq_conj_mul]
    rw [helem, map_mul,
      show Ψ (⟨((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
            * ((lift a : ↥C) : P)⁻¹, hconj_ab⟩ : ↥(⁅C, C⁆))
          = Ψ (⟨⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_b⟩ : ↥(⁅C, C⁆)) from
        hΨconj ((lift a : ↥C) : P) (lift a).2
          ⟨⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_b⟩,
      mul_comm (Ψ (⟨⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_b⟩ : ↥(⁅C, C⁆)))
        (Ψ (⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_a⟩ : ↥(⁅C, C⁆)))]
  have hmul' : ∀ a b d : ↥W, c a (b * d) = c a b * c a d := by
    intro a b d
    have hlift : Φ2 (lift (b * d)) = Φ2 (lift b * lift d) := by
      rw [map_mul, lift_spec, lift_spec, lift_spec]
    have h1 := hwd2 (lift a) (lift (b * d)) (lift b * lift d) hlift
    have hD_a : ⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift a).2 (lift b).2
    have hD_d : ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift a).2 (lift d).2
    have hconj_bd : ((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
        * ((lift b : ↥C) : P)⁻¹ ∈ ⁅C, C⁆ := hDvN.conj_mem _ hD_d _
    rw [hc_apply, hc_apply, hc_apply, h1]
    have helem : (⟨⁅((lift a : ↥C) : P), (((lift b : ↥C) * (lift d : ↥C) : ↥C) : P)⁆,
          Subgroup.commutator_mem_commutator (lift a).2 (lift b * lift d).2⟩ : ↥(⁅C, C⁆))
        = (⟨⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆, hD_a⟩ : ↥(⁅C, C⁆))
          * (⟨((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
              * ((lift b : ↥C) : P)⁻¹, hconj_bd⟩ : ↥(⁅C, C⁆)) := by
      refine Subtype.ext ?_
      show ⁅((lift a : ↥C) : P), (((lift b : ↥C) * (lift d : ↥C) : ↥C) : P)⁆
        = ⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆
          * (((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
              * ((lift b : ↥C) : P)⁻¹)
      rw [Subgroup.coe_mul, commutatorElement_mul_right_eq_mul_conj]
      group
    rw [helem, map_mul,
      show Ψ (⟨((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
            * ((lift b : ↥C) : P)⁻¹, hconj_bd⟩ : ↥(⁅C, C⁆))
          = Ψ (⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_d⟩ : ↥(⁅C, C⁆)) from
        hΨconj ((lift b : ↥C) : P) (lift b).2
          ⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_d⟩]
  have hxiC : ∀ (x : ↥C), h.xi (x:P) ∈ C := by
    intro x
    have hh := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom x.2
    rwa [hCinv] at hh
  let xiC : ↥C → ↥C := fun x => ⟨h.xi (x:P), hxiC x⟩
  have xiC_val : ∀ x : ↥C, ((xiC x : ↥C) : P) = h.xi (x:P) := fun x => rfl
  have hΦ2xi : ∀ x : ↥C, Φ2 (xiC x) = ξW (Φ2 x) := by
    intro x
    refine Subtype.ext ?_
    have e1 : ((Φ2 (xiC x) : ↥W) : P) = (h.xi (x:P)) ^ 2 ^ e := rfl
    have e2 : ((ξW (Φ2 x) : ↥W) : P) = h.xi ((x:P) ^ 2 ^ e) := rfl
    rw [e1, e2]
    exact hphi2_xi (x:P) x.2
  have heq : ∀ a b : ↥W, ξW (c a b) = c (ξW a) (ξW b) := by
    intro a b
    have h2 := hwd1 (lift (ξW a)) (xiC (lift a)) (lift (ξW b))
      ((lift_spec (ξW a)).trans
        ((congrArg ξW (lift_spec a)).symm.trans (hΦ2xi (lift a)).symm))
    have h3 := hwd2 (xiC (lift a)) (lift (ξW b)) (xiC (lift b))
      ((lift_spec (ξW b)).trans
        ((congrArg ξW (lift_spec b)).symm.trans (hΦ2xi (lift b)).symm))
    have hval : (⟨⁅((xiC (lift a) : ↥C) : P), ((xiC (lift b) : ↥C) : P)⁆,
          Subgroup.commutator_mem_commutator (xiC (lift a)).2 (xiC (lift b)).2⟩ : ↥(⁅C, C⁆))
        = (⟨h.xi (⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆), by
            have hh := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom
              (Subgroup.commutator_mem_commutator (lift a).2 (lift b).2)
            rwa [Subgroup.map_commutator C C (h.xi : MulAut P).toMonoidHom, hCinv] at hh⟩
            : ↥(⁅C, C⁆)) := by
      refine Subtype.ext ?_
      show ⁅((xiC (lift a) : ↥C) : P), ((xiC (lift b) : ↥C) : P)⁆
        = h.xi ⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆
      rw [xiC_val (lift a), xiC_val (lift b)]
      exact (map_commutatorElement (h.xi : MulAut P).toMonoidHom _ _).symm
    rw [hc_apply, hc_apply, h2, h3, hval,
      hPsi_xi (⟨⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆,
        Subgroup.commutator_mem_commutator (lift a).2 (lift b).2⟩ : ↥(⁅C, C⁆)),
      ← hc_apply]

  have hDab : ∀ x ∈ ⁅C, C⁆, ∀ y ∈ ⁅C, C⁆, x * y = y * x :=
    fun x hx y hy => hA.abelian x (hDleA hx) y (hDleA hy)
  have hczero : ∀ a b : ↥W, c a b = 1 :=
    equivariant_bihom_trivial hWtwo ξW htransW c hmul hmul' halt heq
  have hΨtriv : ∀ x y : ↥C,
      Ψ ⟨⁅(x:P), (y:P)⁆, Subgroup.commutator_mem_commutator x.2 y.2⟩ = 1 := by
    intro x y
    have h0 := hczero (Φ2 x) (Φ2 y)
    rw [hc_apply] at h0
    have h1 := hwd1 (lift (Φ2 x)) x (lift (Φ2 y)) (by rw [lift_spec])
    have h2' := hwd2 x (lift (Φ2 y)) y (by rw [lift_spec])
    exact (h1.trans h2').symm.trans h0
  have hDsub : ⁅C, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    show ⁅x, y⁆ ∈ Work.Higman.powSub ⁅C, C⁆ 2
    exact (hΨker _).mp (hΨtriv ⟨x, hx⟩ ⟨y, hy⟩)
  have hDpow : ⁅C, C⁆ = Work.Higman.powSub ⁅C, C⁆ 2 :=
    le_antisymm hDsub (powSub_le (by norm_num))
  have hpow : ∀ k : ℕ, Work.Higman.powSub ⁅C, C⁆ (2 ^ k) = ⁅C, C⁆ := by
    intro k
    induction k with
    | zero => rw [pow_zero, powSub_one_eq]
    | succ k ih =>
        rw [pow_succ, ← powSub_powSub hDab (2 ^ k) 2, ih]
        exact hDpow.symm
  have hbotpow : Work.Higman.powSub ⁅C, C⁆ (2 ^ e) = ⊥ :=
    le_bot_iff.mp ((powSub_mono hDleA).trans
      (le_of_eq (powSub_eq_bot_of_exp hA.abelian le_rfl he1)))
  exact hDne (by rw [← hpow e, hbotpow])


end MSA

end Work.Higman
