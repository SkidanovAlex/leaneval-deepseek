import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.cfInner_indFun
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.conjFun_mem_Irr
import Submission.Work.Clifford.autChar_mem_Irr
import Submission.Work.Induction.indFun_trans
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.isChar_indFun
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.exists_nat_cfInner_indFun
import Submission.Work.Induction.exists_nat_cfInner_resFun
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.Bridge
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.fdRep_simple_iff
import Submission.Work.CharCore.classFun_eq_sum_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Clifford correspondence: `Ind_I^G ψ ∈ Irr G` for `ψ` lying over `θ`

For `N ⊴ G`, `θ ∈ Irr N` and `I = I_G(θ)` the inertia group of `θ`, every irreducible
character `ψ` of `I` lying over `θ` induces to an irreducible character of `G` (Clifford's
correspondence, Isaacs 6.11).

The proof does not need Clifford's theorem itself.  Writing `Φ = ind_N^G θ` and letting
`f λ = ⟪λ|_N, θ⟫` (λ ∈ Irr I) and `e χ = ⟪χ|_N, θ⟫` (χ ∈ Irr G) be the multiplicities, one has

* `Φ = Σ_λ f λ • ind_I^G λ` and hence `Σ_χ (e χ)² = ||Φ||² = Σ_λ (f λ)²`, and writing
  `e χ = Σ_λ a(χ,λ) f λ` with `a(χ,λ) = ⟪ind_I^G λ, χ⟫_G ∈ ℕ` this reads
  `Σ_λ (f λ)² = Σ_χ (Σ_λ a(χ,λ) f λ)²`;
* both sides of `Σ_χ (e χ)² = Σ_λ (f λ)²` equal the norm `||ind_N^G θ||² = |I|/|N|`, computed
  for the pair `(G, N)` and for the pair `(I, N.subgroupOf I)` — this is
  `cfInner_indFun_normal'`;
* since `a(χ,λ) ≥ 0` and `Σ_χ a(χ,λ)² ≥ 1` for every λ (as `ind_I^G λ ≠ 0`), the elementary
  inequality `Σ_y (f y)² ≤ Σ_y (f y)² Σ_x a(x,y)² ≤ Σ_x (Σ_y a(x,y) f y)²` is an equality,
  forcing `Σ_χ a(χ,ψ)² = 1` for every `ψ` with `f ψ ≠ 0`.

Hence `ind_I^G ψ` is a virtual character with norm `1`, so (up to sign, ruled out by the value
at `1`) an irreducible character of `G`.
-/

noncomputable section

open Classical

namespace Work.Clifford

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] [Fintype G]

/-! ### Bridging the two vocabularies -/

/-- `Work.Clifford.Irr` and `Work.CharCore.Irr` are the same set of functions. -/
theorem mem_Irr_charCore_iff {χ : G → ℂ} :
    χ ∈ Work.Clifford.Irr G ↔ χ ∈ Work.CharCore.Irr G :=
  (Work.Clifford.mem_Irr).trans (Work.CharCore.mem_Irr_iff_fdrep χ).symm

theorem isChar_of_mem_Irr {χ : G → ℂ} (h : χ ∈ Work.Clifford.Irr G) :
    Work.CharCore.IsChar χ :=
  Work.CharCore.IsChar.of_mem_Irr ((mem_Irr_charCore_iff).mp h)

theorem isVChar_of_mem_Irr {χ : G → ℂ} (h : χ ∈ Work.Clifford.Irr G) :
    Work.CharCore.IsVChar χ :=
  Work.CharCore.IsVChar.of_mem_Irr ((mem_Irr_charCore_iff).mp h)

/-- The normalised inner product is invariant under a group isomorphism. -/
theorem cfInner_comp_mulEquiv {H K : Type*} [Group H] [Fintype H] [Group K] [Fintype K]
    (e : H ≃* K) (f g : K → ℂ) :
    Work.CharCore.cfInner (fun h => f (e h)) (fun h => g (e h)) = Work.CharCore.cfInner f g := by
  have hcard : Fintype.card H = Fintype.card K := Fintype.card_congr e.toEquiv
  rw [Work.CharCore.cfInner_apply, Work.CharCore.cfInner_apply, hcard]
  congr 1
  exact Fintype.sum_equiv e.toEquiv _ _ (fun h => rfl)

/-- The order isomorphism between the subrepresentation lattices of `ρ ∘ e` and `ρ`, for a
surjective monoid homomorphism `e`. -/
def subrepresentationCompOrderIso {H K V : Type*} [Group H] [Group K] [AddCommGroup V]
    [Module ℂ V] (e : H ≃* K) (ρ : Representation ℂ K V) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun k v hv => by
        obtain ⟨h, rfl⟩ := e.surjective k
        exact S.apply_mem_toSubmodule h hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv => S.apply_mem_toSubmodule (e h) hv }
  left_inv S := by ext v; rfl
  right_inv S := by ext v; rfl
  map_rel_iff' := fun {S T} => Iff.rfl

/-- Composing a representation with a bijective monoid homomorphism preserves irreducibility
(expressed with `IsSimpleOrder` to avoid a `Representation`/`MonoidHom` notation clash). -/
theorem isSimpleOrder_subrepresentation_comp {H K V : Type*} [Group H] [Group K] [AddCommGroup V]
    [Module ℂ V] (e : H ≃* K) {ρ : Representation ℂ K V}
    (h : IsSimpleOrder (Subrepresentation ρ)) :
    IsSimpleOrder (Subrepresentation (ρ.comp e.toMonoidHom)) :=
  (subrepresentationCompOrderIso e ρ).isSimpleOrder_iff.mpr h

/-- `Irr` is invariant under group isomorphism. -/
theorem Irr_comp_mulEquiv {H K : Type*} [Group H] [Fintype H] [Group K] [Fintype K]
    (e : H ≃* K) {θ : K → ℂ} (h : θ ∈ Work.Clifford.Irr K) :
    (fun h => θ (e h)) ∈ Work.Clifford.Irr H := by
  obtain ⟨V, hV, hVθ⟩ := (Work.Clifford.mem_Irr).mp h
  refine (Work.Clifford.mem_Irr).mpr ⟨FDRep.of (V.ρ.comp e.toMonoidHom), ?_, ?_⟩
  · rw [Work.CharCore.fdRep_simple_iff, FDRep.of_ρ']
    exact isSimpleOrder_subrepresentation_comp e ((Work.CharCore.fdRep_simple_iff V).mp hV)
  · ext h
    show Representation.character (V.ρ.comp e.toMonoidHom) h = θ (e h)
    rw [← hVθ]
    rfl

/-! ### Parseval and some elementary arithmetic -/

/-- If the inner products of a class function `F` with the irreducible characters are the
natural numbers `n χ`, then the norm of `F` is `∑ (n χ)^2`. -/
theorem cfInner_self_eq_sum_sq {G : Type*} [Group G] [Fintype G] {F : G → ℂ}
    (hF : Work.CharCore.IsClassFun F) (n : ↥(Work.CharCore.Irr G) → ℕ)
    (hn : ∀ χ : ↥(Work.CharCore.Irr G), Work.CharCore.cfInner F (χ : G → ℂ) = (n χ : ℂ)) :
    Work.CharCore.cfInner F F = ∑ χ : ↥(Work.CharCore.Irr G), ((n χ : ℂ)) ^ 2 := by
  have hF' : F = ∑ χ : ↥(Work.CharCore.Irr G), (n χ : ℂ) • (χ : G → ℂ) := by
    rw [Work.CharCore.classFun_eq_sum_irr hF, Finset.sum_subtype (Work.CharCore.Irr G)
        (fun x => Iff.rfl) (fun χ => Work.CharCore.cfInner F χ • χ)]
    exact Finset.sum_congr rfl fun χ _ => by rw [hn χ]
  rw [hF', Work.CharCore.cfInner_sum_smul_left]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Work.CharCore.cfInner_sum_smul_right, Finset.sum_eq_single χ]
  · rw [Work.CharCore.irr_orthonormal_charCore χ.2 χ.2]
    simp [sq]
  · intro b _ hb
    rw [Work.CharCore.irr_orthonormal_charCore χ.2 b.2]
    have hne : ¬ ((χ : G → ℂ) = (b : G → ℂ)) := fun h => hb (Subtype.ext h).symm
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ χ) h

theorem sum_sq_sum_eq {X Y : Type*} [Fintype X] [Fintype Y] (a : X → Y → ℕ) (f : Y → ℕ) :
    ∑ x : X, (∑ y : Y, a x y * f y) ^ 2
      = ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y' := by
  calc ∑ x : X, (∑ y : Y, a x y * f y) ^ 2
      = ∑ x : X, ∑ y : Y, ∑ y' : Y, (a x y * f y) * (a x y' * f y') := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ y : Y, ∑ y' : Y, ∑ x : X, (a x y * f y) * (a x y' * f y') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y' := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring

/-- If `Σ_x (Σ_y a x y * f y)^2 = Σ_y (f y)^2`, all `a x y` are natural numbers and
`1 ≤ Σ_x (a x y)^2` for every `y`, then `Σ_x (a x y)^2 = 1` for every `y` with `f y ≠ 0`. -/
theorem sum_sq_eq_one_of_gram {X Y : Type*} [Fintype X] [Fintype Y] (a : X → Y → ℕ) (f : Y → ℕ)
    (hdiag : ∀ y, 1 ≤ ∑ x : X, a x y * a x y)
    (hkey : ∑ x : X, (∑ y : Y, a x y * f y) ^ 2 = ∑ y : Y, f y * f y) :
    ∀ y, f y ≠ 0 → ∑ x : X, a x y * a x y = 1 := by
  intro y₀ hy₀
  have hgram : ∑ y : Y, f y * f y
      = ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y' := by
    rw [← hkey, sum_sq_sum_eq]
  have h1 : ∑ y : Y, f y * f y * ∑ x : X, a x y * a x y
      ≤ ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y' := by
    refine Finset.sum_le_sum fun y _ => ?_
    exact Finset.single_le_sum (f := fun y' => f y * f y' * ∑ x : X, a x y * a x y')
      (fun y' _ => Nat.zero_le _) (Finset.mem_univ y)
  have h2 : ∑ y : Y, f y * f y ≤ ∑ y : Y, f y * f y * ∑ x : X, a x y * a x y := by
    refine Finset.sum_le_sum fun y _ => ?_
    calc f y * f y = f y * f y * 1 := (mul_one _).symm
      _ ≤ f y * f y * ∑ x : X, a x y * a x y := Nat.mul_le_mul_left _ (hdiag y)
  have heq : ∑ y : Y, f y * f y * ∑ x : X, a x y * a x y = ∑ y : Y, f y * f y :=
    le_antisymm (hgram ▸ h1) (hgram ▸ h2)
  have hle_term : ∀ y ∈ (Finset.univ : Finset Y), f y * f y ≤ f y * f y * ∑ x : X, a x y * a x y :=
    fun y _ => by
      calc f y * f y = f y * f y * 1 := (mul_one _).symm
        _ ≤ f y * f y * ∑ x : X, a x y * a x y := Nat.mul_le_mul_left _ (hdiag y)
  have hterm : f y₀ * f y₀ * ∑ x : X, a x y₀ * a x y₀ = f y₀ * f y₀ :=
    ((Finset.sum_eq_sum_iff_of_le hle_term).1 heq.symm y₀ (Finset.mem_univ y₀)).symm
  have hne : f y₀ * f y₀ ≠ 0 := Nat.mul_ne_zero hy₀ hy₀
  have hterm' : f y₀ * f y₀ * ∑ x : X, a x y₀ * a x y₀ = f y₀ * f y₀ * 1 := by
    rw [mul_one]; exact hterm
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) hterm'

/-- `b * ∑ n_i² = a` from `∑ n_i² = a * b⁻¹`. -/
theorem nat_mul_sum_sq_eq {ι : Type*} [Fintype ι] (n : ι → ℕ) {a b : ℕ} (hb : b ≠ 0)
    (h : ∑ i, ((n i : ℂ)) ^ 2 = (a : ℂ) * (b : ℂ)⁻¹) :
    b * ∑ i, (n i) ^ 2 = a := by
  have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have key : ((b * ∑ i, (n i) ^ 2 : ℕ) : ℂ) = ((a : ℕ) : ℂ) := by
    push_cast
    rw [h, ← mul_assoc, mul_comm (b : ℂ) (a : ℂ), mul_assoc, mul_inv_cancel₀ hb', mul_one]
  exact Nat.cast_injective key

/-! ### The norm of an induced character from a normal subgroup -/

/-- Value of an induced function at an element of the normal subgroup. -/
theorem mul_card_indFun_apply {N : Subgroup G} [N.Normal] (θ : N → ℂ) (n : N) :
    (Nat.card ↥N : ℂ) * Work.Induction.indFun N θ n
      = ∑ x : G, Work.Clifford.conjFun N x θ n := by
  have hN_ne : (Nat.card ↥N : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  rw [Work.Induction.indFun_apply_def]
  rw [← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dite_eq_left ((inferInstance : N.Normal).conj_mem (n : G) n.2 x)]
  rfl

/-- **Norm of an induced character from a normal subgroup**: for `N ⊴ G` and `θ ∈ Irr N`,
`⟪Ind_N^G θ, Ind_N^G θ⟫_G = |I_G(θ)| / |N|`. -/
theorem cfInner_indFun_normal' {N : Subgroup G} [N.Normal] {θ : N → ℂ}
    (hθ : θ ∈ Work.Clifford.Irr N) :
    Work.CharCore.cfInner (Work.Induction.indFun N θ) (Work.Induction.indFun N θ)
      = (Nat.card ↥(Work.Clifford.inertia N θ) : ℂ) * (Nat.card ↥N : ℂ)⁻¹ := by
  classical
  have hN_ne : (Nat.card ↥N : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  have hclass : Work.CharCore.IsClassFun (Work.Induction.indFun N θ) :=
    Work.Induction.isClassFun_indFun N θ
  have hθC : θ ∈ Work.CharCore.Irr N := (mem_Irr_charCore_iff).mp hθ
  have hconjC : ∀ x : G, Work.Clifford.conjFun N x θ ∈ Work.CharCore.Irr N := fun x =>
    (mem_Irr_charCore_iff).mp (Work.Clifford.conjFun_mem_Irr x hθ)
  have hstep : ∀ n : N, Work.Induction.indFun N θ n
      = (Nat.card ↥N : ℂ)⁻¹ * ∑ x : G, Work.Clifford.conjFun N x θ n := by
    intro n
    have h := mul_card_indFun_apply (G := G) θ n
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hN_ne, one_mul]
  have hkey : ∀ n : N, θ n * starRingEnd ℂ (Work.Induction.indFun N θ n)
      = (Nat.card ↥N : ℂ)⁻¹ * ∑ x : G, θ n * starRingEnd ℂ (Work.Clifford.conjFun N x θ n) := by
    intro n
    have h1 : starRingEnd ℂ (Work.Induction.indFun N θ n)
        = (Nat.card ↥N : ℂ)⁻¹ * ∑ x : G, starRingEnd ℂ (Work.Clifford.conjFun N x θ n) := by
      rw [hstep n, map_mul, map_inv₀, map_natCast, map_sum]
    rw [h1]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hconj : ∀ x : G, ∑ n : N, θ n * starRingEnd ℂ (Work.Clifford.conjFun N x θ n)
      = (Nat.card ↥N : ℂ) * Work.CharCore.cfInner θ (Work.Clifford.conjFun N x θ) := by
    intro x
    rw [Work.CharCore.cfInner_apply, ← Nat.card_eq_fintype_card]
    rw [← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul]
  have horth : ∀ x : G, Work.CharCore.cfInner θ (Work.Clifford.conjFun N x θ)
      = if θ = Work.Clifford.conjFun N x θ then 1 else 0 := fun x =>
    Work.CharCore.irr_orthonormal_charCore hθC (hconjC x)
  have hind : ∑ x : G, (if θ = Work.Clifford.conjFun N x θ then (1 : ℂ) else 0)
      = (Nat.card ↥(Work.Clifford.inertia N θ) : ℂ) := by
    have hcard : (Finset.univ.filter (fun x : G => θ = Work.Clifford.conjFun N x θ)).card
        = Fintype.card ↥(Work.Clifford.inertia N θ) := by
      rw [← Fintype.card_subtype (fun x : G => θ = Work.Clifford.conjFun N x θ)]
      exact Fintype.card_congr
        (Equiv.subtypeEquivRight fun x => eq_comm.trans (Work.Clifford.mem_inertia N θ x).symm)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hcard,
      Nat.card_eq_fintype_card]
  have hsum : ∑ n : N, θ n * starRingEnd ℂ (Work.Induction.indFun N θ n)
      = (Nat.card ↥(Work.Clifford.inertia N θ) : ℂ) := by
    have h1 : ∑ n : N, θ n * starRingEnd ℂ (Work.Induction.indFun N θ n)
        = (Nat.card ↥N : ℂ)⁻¹
          * ∑ x : G, ∑ n : N, θ n * starRingEnd ℂ (Work.Clifford.conjFun N x θ n) := by
      rw [Finset.sum_congr rfl (fun n _ => hkey n), ← Finset.mul_sum, Finset.sum_comm]
    rw [h1]
    have h2 : ∀ x : G, ∑ n : N, θ n * starRingEnd ℂ (Work.Clifford.conjFun N x θ n)
        = (Nat.card ↥N : ℂ) * (if θ = Work.Clifford.conjFun N x θ then 1 else 0) := by
      intro x
      rw [hconj x, horth x]
    rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.mul_sum, hind, ← mul_assoc,
      inv_mul_cancel₀ hN_ne, one_mul]
  rw [Work.Induction.frobenius_reciprocity (H := N) θ (Work.Induction.indFun N θ) hclass,
    Work.CharCore.cfInner_apply]
  simp only [Work.Induction.resFun_apply]
  rw [hsum, mul_comm]
  simp only [Nat.card_eq_fintype_card]

/-! ### The invariance of the transported character -/

/-- The transported function `θ ∘ e` on `N.subgroupOf I` is invariant under `I`. -/
theorem conjFun_subgroupOf_apply {N : Subgroup G} [N.Normal] {I : Subgroup G}
    (f : ↥(N.subgroupOf I) → ℂ) (i : ↥I) (x : ↥(N.subgroupOf I)) :
    Work.Clifford.conjFun (N.subgroupOf I) i f x = f ⟨i * (x : ↥I) * i⁻¹,
      (inferInstance : (N.subgroupOf I).Normal).conj_mem (x : ↥I) x.2 i⟩ := rfl

theorem conjFun_subgroupOf_eq {N : Subgroup G} [N.Normal] {θ : N → ℂ}
    {I : Subgroup G} (hI : N ≤ I) (i : ↥I)
    (hi : Work.Clifford.conjFun N (i : G) θ = θ) :
    Work.Clifford.conjFun (N.subgroupOf I) i
        (fun x : ↥(N.subgroupOf I) => θ (Subgroup.subgroupOfEquivOfLe hI x))
      = (fun x : ↥(N.subgroupOf I) => θ (Subgroup.subgroupOfEquivOfLe hI x)) := by
  funext x
  rw [conjFun_subgroupOf_apply]
  have h2 : θ (Subgroup.subgroupOfEquivOfLe hI ⟨i * (x : ↥I) * i⁻¹,
        (inferInstance : (N.subgroupOf I).Normal).conj_mem (x : ↥I) x.2 i⟩)
      = Work.Clifford.conjFun N (i : G) θ (Subgroup.subgroupOfEquivOfLe hI x) := by
    rw [Work.Clifford.conjFun]
    congr 1
  rw [h2, hi]


/-! ### The main norm computation -/

/-- **The norm of `Ind_I^G ψ` is one** for `ψ ∈ Irr I`, `I = I_G(θ)`, `ψ` lying over `θ`. -/
theorem cfInner_indFun_inertia_eq_one {N : Subgroup G} [N.Normal] {θ : N → ℂ}
    (hθ : θ ∈ Work.Clifford.Irr N)
    {ψ : ↥(Work.Clifford.inertia N θ) → ℂ}
    (hψ : ψ ∈ Work.Clifford.Irr ↥(Work.Clifford.inertia N θ))
    (hlie : Work.Clifford.cfInner
      (Work.Clifford.resFunOfLe (Work.Clifford.le_inertia_of_mem_Irr hθ) ψ) θ ≠ 0) :
    Work.CharCore.cfInner (Work.Induction.indFun (Work.Clifford.inertia N θ) ψ)
      (Work.Induction.indFun (Work.Clifford.inertia N θ) ψ) = 1 := by
  classical
  have hNI : N ≤ Work.Clifford.inertia N θ := Work.Clifford.le_inertia_of_mem_Irr hθ
  have hθC : θ ∈ Work.CharCore.Irr N := (mem_Irr_charCore_iff).mp hθ
  have hψC : ψ ∈ Work.CharCore.Irr ↥(Work.Clifford.inertia N θ) := (mem_Irr_charCore_iff).mp hψ
  have hNcard : Nat.card ↥N ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  -- the transported character `θI` on `N.subgroupOf I`
  let θI : ↥(N.subgroupOf (Work.Clifford.inertia N θ)) → ℂ :=
    fun x => θ (Subgroup.subgroupOfEquivOfLe hNI x)
  have hθI : θI ∈ Work.Clifford.Irr ↥(N.subgroupOf (Work.Clifford.inertia N θ)) :=
    Irr_comp_mulEquiv (Subgroup.subgroupOfEquivOfLe hNI) hθ
  have hθIC : θI ∈ Work.CharCore.Irr ↥(N.subgroupOf (Work.Clifford.inertia N θ)) :=
    (mem_Irr_charCore_iff).mp hθI
  have hinv : Work.Clifford.inertia (N.subgroupOf (Work.Clifford.inertia N θ)) θI = ⊤ := by
    ext i
    rw [Work.Clifford.mem_inertia]
    exact ⟨fun _ => Subgroup.mem_top i,
      fun _ => conjFun_subgroupOf_eq hNI i ((Work.Clifford.mem_inertia N θ (i : G)).mp i.2)⟩
  -- the multiplicities
  have hfex : ∀ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), ∃ n : ℕ,
      Work.CharCore.cfInner (Work.Induction.resFun (N.subgroupOf (Work.Clifford.inertia N θ))
        (y : ↥(Work.Clifford.inertia N θ) → ℂ)) θI = (n : ℂ) := fun y =>
    Work.Induction.exists_nat_cfInner_resFun (H := N.subgroupOf (Work.Clifford.inertia N θ))
      (χ := (y : ↥(Work.Clifford.inertia N θ) → ℂ)) y.2 (θ := θI) hθIC
  choose f hf using hfex
  have heex : ∀ χ : ↥(Work.CharCore.Irr G), ∃ n : ℕ,
      Work.CharCore.cfInner (Work.Induction.resFun N (χ : G → ℂ)) θ = (n : ℂ) := fun χ =>
    Work.Induction.exists_nat_cfInner_resFun (H := N) (χ := (χ : G → ℂ)) χ.2 (θ := θ) hθC
  choose e he using heex
  have haex : ∀ χ : ↥(Work.CharCore.Irr G),
      ∀ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), ∃ n : ℕ,
      Work.CharCore.cfInner (Work.Induction.indFun (Work.Clifford.inertia N θ)
        (y : ↥(Work.Clifford.inertia N θ) → ℂ)) (χ : G → ℂ) = (n : ℂ) := fun χ y =>
    Work.Induction.exists_nat_cfInner_indFun (H := Work.Clifford.inertia N θ)
      (θ := (y : ↥(Work.Clifford.inertia N θ) → ℂ)) y.2 (χ := (χ : G → ℂ)) χ.2
  choose a ha using haex
  -- the norm at the level of `I`
  have hnormI : Work.CharCore.cfInner
        (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI)
        (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI)
      = (Nat.card ↥(Work.Clifford.inertia N θ) : ℂ) * (Nat.card ↥N : ℂ)⁻¹ := by
    rw [cfInner_indFun_normal' (θ := θI) hθI, hinv]
    have h1 : Nat.card ↥(⊤ : Subgroup ↥(Work.Clifford.inertia N θ))
        = Nat.card ↥(Work.Clifford.inertia N θ) := by simp
    have h2 : Nat.card ↥(N.subgroupOf (Work.Clifford.inertia N θ)) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNI).toEquiv
    rw [h1, h2]
  -- the expansion of `ind_N^I θI`
  have hclassI : Work.CharCore.IsClassFun
      (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI) :=
    Work.Induction.isClassFun_indFun _ _
  have hfrec : ∀ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)),
      Work.CharCore.cfInner
        (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI)
        (y : ↥(Work.Clifford.inertia N θ) → ℂ) = (f y : ℂ) := by
    intro y
    rw [Work.Induction.frobenius_reciprocity (H := N.subgroupOf (Work.Clifford.inertia N θ))
        θI (y : ↥(Work.Clifford.inertia N θ) → ℂ) (Work.CharCore.isClassFun_of_mem_Irr y.2),
      Work.CharCore.cfInner_conj_symm, hf y]
    simp
  have hexpI : Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI
      = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)),
          (f y : ℂ) • (y : ↥(Work.Clifford.inertia N θ) → ℂ) := by
    rw [Work.CharCore.classFun_eq_sum_irr hclassI]
    rw [Finset.sum_subtype (Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)) (fun x => Iff.rfl)
      (fun y => Work.CharCore.cfInner
        (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI) y • y)]
    exact Finset.sum_congr rfl fun y _ => by rw [hfrec y]
  -- Parseval at both levels
  have hsumG : Work.CharCore.cfInner (Work.Induction.indFun N θ) (Work.Induction.indFun N θ)
      = ∑ χ : ↥(Work.CharCore.Irr G), ((e χ : ℕ) : ℂ) ^ 2 := by
    refine cfInner_self_eq_sum_sq (Work.Induction.isClassFun_indFun N θ) e ?_
    intro χ
    rw [Work.Induction.frobenius_reciprocity (H := N) θ (χ : G → ℂ)
        (Work.CharCore.isClassFun_of_mem_Irr χ.2), Work.CharCore.cfInner_conj_symm, he χ]
    simp
  have hsumI : Work.CharCore.cfInner
        (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI)
        (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI)
      = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), ((f y : ℕ) : ℂ) ^ 2 :=
    cfInner_self_eq_sum_sq hclassI f hfrec
  have hEG : Nat.card ↥N * ∑ χ : ↥(Work.CharCore.Irr G), (e χ) ^ 2
      = Nat.card ↥(Work.Clifford.inertia N θ) :=
    nat_mul_sum_sq_eq e hNcard (hsumG.symm.trans (cfInner_indFun_normal' hθ))
  have hEI : Nat.card ↥N * ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), (f y) ^ 2
      = Nat.card ↥(Work.Clifford.inertia N θ) :=
    nat_mul_sum_sq_eq f hNcard (hsumI.symm.trans hnormI)
  have hsumeq : ∑ χ : ↥(Work.CharCore.Irr G), (e χ) ^ 2
      = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), (f y) ^ 2 :=
    Nat.mul_left_cancel (Nat.pos_of_ne_zero hNcard) (hEG.trans hEI.symm)
  -- the expansion of `ind_I^G y`
  have hExpy : ∀ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)),
      Work.Induction.indFun (Work.Clifford.inertia N θ)
          (y : ↥(Work.Clifford.inertia N θ) → ℂ)
        = ∑ χ : ↥(Work.CharCore.Irr G), (a χ y : ℂ) • (χ : G → ℂ) := by
    intro y
    rw [Work.CharCore.classFun_eq_sum_irr (Work.Induction.isClassFun_indFun _ _)]
    rw [Finset.sum_subtype (Work.CharCore.Irr G) (fun x => Iff.rfl)
      (fun χ => Work.CharCore.cfInner (Work.Induction.indFun (Work.Clifford.inertia N θ)
        (y : ↥(Work.Clifford.inertia N θ) → ℂ)) χ • χ)]
    exact Finset.sum_congr rfl fun χ _ => by rw [ha χ y]
  -- transitivity of induction
  have htrans : Work.Induction.indFun (Work.Clifford.inertia N θ)
        (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI)
      = Work.Induction.indFun N θ :=
    Work.Induction.indFun_trans hNI θ
  -- the multiplicities of `ind_I^G y` in `ind_N^G θ`
  have hK3 : ∀ χ : ↥(Work.CharCore.Irr G),
      (e χ : ℂ) = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)),
        (a χ y : ℂ) * (f y : ℂ) := by
    intro χ
    have h1 : Work.CharCore.cfInner (Work.Induction.indFun N θ) (χ : G → ℂ) = (e χ : ℂ) := by
      rw [Work.Induction.frobenius_reciprocity (H := N) θ (χ : G → ℂ)
          (Work.CharCore.isClassFun_of_mem_Irr χ.2), Work.CharCore.cfInner_conj_symm, he χ]
      simp
    have h2 : Work.CharCore.cfInner (Work.Induction.indFun N θ) (χ : G → ℂ)
        = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)),
            (a χ y : ℂ) * (f y : ℂ) := by
      rw [← htrans,
        Work.Induction.frobenius_reciprocity (H := Work.Clifford.inertia N θ)
          (Work.Induction.indFun (N.subgroupOf (Work.Clifford.inertia N θ)) θI) (χ : G → ℂ)
          (Work.CharCore.isClassFun_of_mem_Irr χ.2)]
      rw [hexpI, Work.CharCore.cfInner_sum_smul_left]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Work.Induction.frobenius_reciprocity (H := Work.Clifford.inertia N θ)
        (y : ↥(Work.Clifford.inertia N θ) → ℂ) (χ : G → ℂ)
        (Work.CharCore.isClassFun_of_mem_Irr χ.2), ha χ y]
      ring
    rw [← h1, h2]
  have hK3n : ∀ χ : ↥(Work.CharCore.Irr G),
      e χ = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), a χ y * f y := by
    intro χ
    have key : (e χ : ℂ) = ((∑ y, a χ y * f y : ℕ) : ℂ) := by
      rw [Nat.cast_sum, hK3 χ]
      exact Finset.sum_congr rfl fun y _ => by push_cast; ring
    exact Nat.cast_injective key
  have hsumeq' : ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), f y ^ 2
      = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), f y * f y :=
    Finset.sum_congr rfl fun y _ => by rw [sq]
  have hkey : ∑ χ : ↥(Work.CharCore.Irr G),
        (∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), a χ y * f y) ^ 2
      = ∑ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)), f y * f y := by
    rw [← hsumeq', ← hsumeq]
    exact Finset.sum_congr rfl fun χ _ => by rw [← hK3n χ]
  -- `ind_I^G y ≠ 0`, so `Σ_χ a χ y * a χ y ≥ 1`
  have hindex_ne : (Work.Clifford.inertia N θ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hdiag : ∀ y : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)),
      1 ≤ ∑ χ : ↥(Work.CharCore.Irr G), a χ y * a χ y := by
    intro y
    by_contra hlt
    have hzero : ∑ χ : ↥(Work.CharCore.Irr G), a χ y * a χ y = 0 := by omega
    have hzero' : ∀ χ : ↥(Work.CharCore.Irr G), a χ y = 0 := by
      intro χ
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun χ _ => Nat.zero_le _)).mp hzero χ
        (Finset.mem_univ χ)
      exact (Nat.mul_eq_zero.mp h).elim id id
    have hfun : Work.Induction.indFun (Work.Clifford.inertia N θ)
        (y : ↥(Work.Clifford.inertia N θ) → ℂ) = 0 := by
      rw [hExpy y]
      simp [hzero']
    have hval : Work.Induction.indFun (Work.Clifford.inertia N θ)
        (y : ↥(Work.Clifford.inertia N θ) → ℂ) 1 ≠ 0 := by
      rw [Work.Induction.indFun_apply_one, Work.CharCore.irrDeg_spec y.2]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hindex_ne) (Work.CharCore.irrDeg_ne_zero y.2)
    exact hval (by rw [hfun]; rfl)
  -- the hypothesis `f ψ ≠ 0`
  have hfψ : f (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ))) ≠ 0 := by
    intro h0
    apply hlie
    have hbr : Work.CharCore.cfInner
        (Work.Induction.resFun (N.subgroupOf (Work.Clifford.inertia N θ)) ψ) θI
        = Work.Clifford.cfInner (Work.Clifford.resFunOfLe hNI ψ) θ := by
      have h1 : Work.Induction.resFun (N.subgroupOf (Work.Clifford.inertia N θ)) ψ
          = fun x => (Work.Clifford.resFunOfLe hNI ψ)
              (Subgroup.subgroupOfEquivOfLe hNI x) := by
        funext x
        exact congrArg ψ (Subtype.ext rfl)
      rw [h1]
      exact cfInner_comp_mulEquiv (Subgroup.subgroupOfEquivOfLe hNI)
        (Work.Clifford.resFunOfLe hNI ψ) θ
    rw [← hbr, hf (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)))]
    exact_mod_cast h0
  have hfinal : ∑ χ : ↥(Work.CharCore.Irr G),
      a χ (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)))
        * a χ (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ))) = 1 :=
    sum_sq_eq_one_of_gram a f hdiag hkey _ hfψ
  have hM : Work.CharCore.cfInner (Work.Induction.indFun (Work.Clifford.inertia N θ) ψ)
      (Work.Induction.indFun (Work.Clifford.inertia N θ) ψ)
      = ∑ χ : ↥(Work.CharCore.Irr G),
          ((a χ (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ))) : ℂ)) ^ 2 := by
    refine cfInner_self_eq_sum_sq (Work.Induction.isClassFun_indFun _ _)
      (fun χ => a χ (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)))) ?_
    intro χ
    exact ha χ ⟨ψ, hψC⟩
  rw [hM]
  have hfinalC : ((∑ χ : ↥(Work.CharCore.Irr G),
      a χ (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ)))
        * a χ (⟨ψ, hψC⟩ : ↥(Work.CharCore.Irr ↥(Work.Clifford.inertia N θ))) : ℕ) : ℂ) = 1 := by
    rw [hfinal]
    norm_num
  rw [← hfinalC, Nat.cast_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  push_cast
  ring


/-- **Clifford's correspondence.** For `N ⊴ G`, `θ ∈ Irr N` with inertia group `I = I_G(θ)`,
every irreducible character `ψ` of `I` lying over `θ` induces to an irreducible character
of `G`. -/
theorem clifford_induction_mem_Irr {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) {ψ : (Work.Clifford.inertia N θ) → ℂ}
    (hψ : ψ ∈ Work.Clifford.Irr (Work.Clifford.inertia N θ))
    (hlie : Work.Clifford.LiesOver N (Work.Clifford.inertia N θ)
      (Work.Clifford.le_inertia_of_mem_Irr hθ) θ ψ) :
    Work.Clifford.indFun (Work.Clifford.inertia N θ) ψ ∈ Work.Clifford.Irr G := by
  classical
  have hψC : ψ ∈ Work.CharCore.Irr ↥(Work.Clifford.inertia N θ) :=
    (mem_Irr_charCore_iff (G := ↥(Work.Clifford.inertia N θ))).mp hψ
  -- the norm of the induced character is `1`
  have hnorm : Work.CharCore.cfInner
      (Work.Induction.indFun (Work.Clifford.inertia N θ) ψ)
      (Work.Induction.indFun (Work.Clifford.inertia N θ) ψ) = 1 :=
    cfInner_indFun_inertia_eq_one (G := G) (N := N) hθ hψ hlie
  -- it is a virtual character of norm one
  have hV : Work.CharCore.IsVChar (Work.Induction.indFun (Work.Clifford.inertia N θ) ψ) :=
    Work.Induction.isVChar_indFun (Work.CharCore.IsVChar.of_mem_Irr hψC)
  obtain ⟨χ, hχ, hcase⟩ := Work.CharCore.vchar_norm_one hV hnorm
  -- the sign is positive: evaluate at `1`
  have hidx : ((Work.Clifford.inertia N θ).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Subgroup.index_ne_zero_of_finite)
  have hposcase : Work.Induction.indFun (Work.Clifford.inertia N θ) ψ = χ := by
    rcases hcase with h | h
    · exact h
    · exfalso
      have h1 : Work.Induction.indFun (Work.Clifford.inertia N θ) ψ 1 = -χ 1 := by
        rw [h]; rfl
      rw [Work.Induction.indFun_apply_one, Work.CharCore.irrDeg_spec hψC,
        Work.CharCore.irrDeg_spec hχ] at h1
      have h2 : ((Work.Clifford.inertia N θ).index : ℝ) * (Work.CharCore.irrDeg ψ : ℝ)
          = -((Work.CharCore.irrDeg χ : ℝ)) := by
        apply Complex.ofReal_injective
        push_cast
        exact h1
      have h4 : (0 : ℝ) < ((Work.Clifford.inertia N θ).index : ℝ)
          * (Work.CharCore.irrDeg ψ : ℝ) :=
        mul_pos (Nat.cast_pos.mpr
            (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)))
          (Work.CharCore.irrDeg_pos' hψC)
      have h5 : (0 : ℝ) < (Work.CharCore.irrDeg χ : ℝ) := Work.CharCore.irrDeg_pos' hχ
      linarith
  have hpos' : Work.Clifford.indFun (Work.Clifford.inertia N θ) ψ = χ := hposcase
  rw [hpos']
  exact (mem_Irr_charCore_iff (G := G)).mpr hχ

end Work.Clifford
