import Mathlib
import Submission.Commons.GroupTheory.PGroup.burnside_basis
import Submission.Commons.GroupTheory.Nilpotent.isNilpotent_iff_commutator_le_frattini
import Submission.Commons.GroupTheory.Frattini.frattini_quotient_eq_map
import Submission.Commons.GroupTheory.PGroup.pow_mem_frattini
import Submission.Commons.GroupTheory.PGroup.frattini_eq_pow_sup_commutator
import Submission.Commons.GroupTheory.Commutator.card_mul_card_sq_le_of_alternating_pairing
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_inequality_conclusion


noncomputable section
open MonoidAlgebra

namespace Commons.GroupTheory.ProPGroup

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α]

/-- The free group algebra `F_p[FreeGroup α]`. -/
abbrev WG := MonoidAlgebra (ZMod p) (FreeGroup α)

/-- The image of a group element in the group algebra. -/
local notation "MO" => MonoidAlgebra.of (ZMod p) (FreeGroup α)

/-- The augmentation `F_p[FreeGroup α] → F_p`. -/
noncomputable def gsAug : WG p α →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) (FreeGroup α) (1 : FreeGroup α →* ZMod p)

/-- The augmentation ideal. -/
def gsIW : Ideal (WG p α) := RingHom.ker (gsAug p α).toRingHom

lemma gsAug_of (g : FreeGroup α) : gsAug p α (MO g) = 1 := by
  simp [gsAug]

lemma gsAug_one : gsAug p α (1 : WG p α) = 1 := map_one _

lemma gsIW_mem_iff (z : WG p α) : z ∈ gsIW p α ↔ gsAug p α z = 0 := Iff.rfl

lemma sub_one_mem_gsIW (g : FreeGroup α) : MO g - 1 ∈ gsIW p α := by
  rw [gsIW_mem_iff, map_sub, gsAug_of, gsAug_one, sub_self]

instance instIsTwoSidedGSIW : (gsIW p α).IsTwoSided := by
  refine Ideal.IsTwoSided.mk (fun b ha => ?_)
  rw [gsIW, RingHom.mem_ker] at ha ⊢
  rw [map_mul, ha, zero_mul]

lemma gsIW_sq_eq : gsIW p α ^ 2 = gsIW p α * gsIW p α := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Submodule.pow_succ, Submodule.pow_one]

instance instIsTwoSidedGSIW2 : (gsIW p α ^ 2).IsTwoSided := by
  rw [gsIW_sq_eq]
  refine Ideal.IsTwoSided.mk (fun b ha => ?_)
  have hle : (gsIW p α * gsIW p α) * (⊤ : Ideal (WG p α)) ≤ gsIW p α * gsIW p α := by
    rw [Ideal.mul_assoc, Ideal.mul_top (gsIW p α)]
  exact hle (Submodule.mul_mem_mul ha Submodule.mem_top)

/-- `MO g - 1` raised to the appropriate power lies in `IW^k` when `MO g - 1 ∈ IW`. -/
lemma pow_mem_gsIW (k : ℕ) {x : WG p α} (hx : x ∈ gsIW p α) : x ^ k ∈ gsIW p α ^ k :=
  Ideal.pow_mem_pow hx k

/-- The commutator identity: `MO [a,b] - 1 = ((MO a - 1)(MO b - 1) - (MO b - 1)(MO a - 1)) * MO (ba)⁻¹`. -/
lemma commutator_sub_one_eq (a b : FreeGroup α) :
    MO (a * b * a⁻¹ * b⁻¹) - 1
      = ((MO a - 1) * (MO b - 1) - (MO b - 1) * (MO a - 1)) * MO ((b * a)⁻¹) := by
  have h1 : MO a * MO b - MO b * MO a
      = (MO a - 1) * (MO b - 1) - (MO b - 1) * (MO a - 1) := by noncomm_ring
  have h2 : MO (b * a) * MO ((b * a)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one, MonoidAlgebra.one_def]
  rw [← h1]
  calc MO (a * b * a⁻¹ * b⁻¹) - 1
      = MO (a * b * (b * a)⁻¹) - 1 := by
        congr 2
        group
    _ = MO (a * b) * MO ((b * a)⁻¹) - 1 := by rw [map_mul]
    _ = MO (a * b) * MO ((b * a)⁻¹) - MO (b * a) * MO ((b * a)⁻¹) := by rw [← h2]
    _ = (MO (a * b) - MO (b * a)) * MO ((b * a)⁻¹) := by rw [sub_mul]
    _ = (MO a * MO b - MO b * MO a) * MO ((b * a)⁻¹) := by rw [map_mul, map_mul]

lemma commutator_sub_one_mem_gsIW_sq (a b : FreeGroup α) :
    MO (a * b * a⁻¹ * b⁻¹) - 1 ∈ gsIW p α ^ 2 := by
  rw [commutator_sub_one_eq, gsIW_sq_eq]
  refine Ideal.mul_mem_right _ _ ?_
  refine Ideal.sub_mem _ ?_ ?_
  · exact Ideal.mul_mem_mul (sub_one_mem_gsIW p α a) (sub_one_mem_gsIW p α b)
  · exact Ideal.mul_mem_mul (sub_one_mem_gsIW p α b) (sub_one_mem_gsIW p α a)

lemma mul_sub_one_mem_gsIW_sq {g h : FreeGroup α}
    (hg : MO g - 1 ∈ gsIW p α ^ 2) (hh : MO h - 1 ∈ gsIW p α ^ 2) :
    MO (g * h) - 1 ∈ gsIW p α ^ 2 := by
  rw [map_mul]
  have : MO g * MO h - 1 = MO g * (MO h - 1) + (MO g - 1) := by noncomm_ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hh) hg

lemma inv_sub_one_mem_gsIW_sq {g : FreeGroup α} (hg : MO g - 1 ∈ gsIW p α ^ 2) :
    MO g⁻¹ - 1 ∈ gsIW p α ^ 2 := by
  have h2 : MO g * MO g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one, MonoidAlgebra.one_def]
  have h2' : MO g⁻¹ * MO g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one, MonoidAlgebra.one_def]
  have key : MO g⁻¹ - 1 = -MO g⁻¹ * (MO g - 1) := by
    have hk : -MO g⁻¹ * (MO g - 1) = -(MO g⁻¹ * MO g) + MO g⁻¹ := by noncomm_ring
    rw [hk, h2']
    abel
  rw [key]
  exact Ideal.mul_mem_left _ _ hg

lemma pow_sub_one_mem_gsIW_sq (g : FreeGroup α) :
    MO (g ^ p) - 1 ∈ gsIW p α ^ 2 := by
  rw [map_pow, ← mul_geom_sum (MO g) p, gsIW_sq_eq]
  refine Ideal.mul_mem_mul (sub_one_mem_gsIW p α g) ?_
  rw [gsIW_mem_iff, map_sum]
  have h1 : ∀ i : ℕ, gsAug p α ((MO g) ^ i) = 1 := by
    intro i
    rw [map_pow, gsAug_of, one_pow]
  simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact ZMod.natCast_self p

/-- The subgroup of `FreeGroup α` of elements whose group-algebra augmentation-ideal element
has order at least two: `H = {g | MO g - 1 ∈ IW²}`. -/
def gsH : Subgroup (FreeGroup α) where
  carrier := {g | MO g - 1 ∈ gsIW p α ^ 2}
  one_mem' := by
    show MO 1 - 1 ∈ gsIW p α ^ 2
    rw [map_one, sub_self]
    exact Submodule.zero_mem _
  mul_mem' := fun ha hb => mul_sub_one_mem_gsIW_sq p α ha hb
  inv_mem' := fun ha => inv_sub_one_mem_gsIW_sq p α ha

lemma mem_gsH_iff (g : FreeGroup α) : g ∈ gsH p α ↔ MO g - 1 ∈ gsIW p α ^ 2 := Iff.rfl

lemma commutator_mem_gsH (a b : FreeGroup α) : a * b * a⁻¹ * b⁻¹ ∈ gsH p α :=
  commutator_sub_one_mem_gsIW_sq p α a b

lemma pow_mem_gsH (g : FreeGroup α) : g ^ p ∈ gsH p α :=
  pow_sub_one_mem_gsIW_sq p α g

/-- The "Frattini-like" subgroup generated by commutators and `p`-th powers:
`Φ = ⟨⁅a,b⁆, g^p⟩`.  The minimality of the presentation will give `π.ker ≤ Φ`. -/
def gsPhi : Subgroup (FreeGroup α) :=
  Subgroup.closure ({x : FreeGroup α | ∃ a b : FreeGroup α, x = a * b * a⁻¹ * b⁻¹} ∪
    {x : FreeGroup α | ∃ g : FreeGroup α, x = g ^ p})

lemma commutatorSet_le_gsH :
    Subgroup.closure ({x : FreeGroup α | ∃ a b : FreeGroup α, x = a * b * a⁻¹ * b⁻¹})
      ≤ gsH p α :=
  (Subgroup.closure_le (gsH p α)).mpr (by rintro x ⟨a, b, rfl⟩; exact commutator_mem_gsH p α a b)

lemma powSet_le_gsH :
    Subgroup.closure ({x : FreeGroup α | ∃ g : FreeGroup α, x = g ^ p}) ≤ gsH p α :=
  (Subgroup.closure_le (gsH p α)).mpr (by rintro x ⟨g, rfl⟩; exact pow_mem_gsH p α g)

lemma gsPhi_le_gsH : gsPhi p α ≤ gsH p α := by
  rw [gsPhi]
  exact (Subgroup.closure_le (gsH p α)).mpr (by
    rintro x (hx | hx)
    · exact commutatorSet_le_gsH p α (Subgroup.subset_closure hx)
    · exact powSet_le_gsH p α (Subgroup.subset_closure hx))

lemma sub_one_mem_gsIW_sq_of_mem_gsPhi {g : FreeGroup α} (hg : g ∈ gsPhi p α) :
    MO g - 1 ∈ gsIW p α ^ 2 :=
  gsPhi_le_gsH p α hg

/-- **Hand-off lemma.**  As soon as `N ≤ Φ` (which the minimality of the presentation supplies),
every element of `N` gives an element of `IW²`. -/
lemma sub_one_mem_gsIW_sq_of_le_gsPhi {N : Subgroup (FreeGroup α)} (hN : N ≤ gsPhi p α)
    {g : FreeGroup α} (hg : g ∈ N) : MO g - 1 ∈ gsIW p α ^ 2 :=
  gsPhi_le_gsH p α (hN hg)


end Commons.GroupTheory.ProPGroup

-- ===== end of gsSerre_IW2 =====


open scoped commutatorElement

noncomputable section

namespace Commons.GroupTheory.ProPGroup

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α]

/-- The Frattini-like subgroup of the free group generated by commutators and `p`-th powers. -/
def gsPhiF : Subgroup (FreeGroup α) :=
  Subgroup.closure ({x : FreeGroup α | ∃ a b : FreeGroup α, x = a * b * a⁻¹ * b⁻¹} ∪
    {x : FreeGroup α | ∃ g : FreeGroup α, x = g ^ p})

/-- The image of a commutator is a commutator. -/
lemma map_commutator_eq {G : Type*} [Group G] (π : FreeGroup α →* G) (a b : FreeGroup α) :
    π (a * b * a⁻¹ * b⁻¹) = π a * π b * (π a)⁻¹ * (π b)⁻¹ := by
  simp only [map_mul, map_inv]

/-- The image of a `p`-th power is a `p`-th power. -/
lemma map_pow_eq {G : Type*} [Group G] (π : FreeGroup α →* G) (g : FreeGroup α) :
    π (g ^ p) = (π g) ^ p := map_pow π g p

/-- For a finite `p`-group, the commutator subgroup lies in the Frattini subgroup. -/
lemma commutator_le_frattini {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) :
    _root_.commutator G ≤ frattini G :=
  (Commons.GroupTheory.Nilpotent.isNilpotent_iff_commutator_le_frattini (G := G)).mp
    hG.isNilpotent

/-- The commutator half: the image of the commutator-generated subgroup lies in `frattini G`. -/
lemma map_commutatorSet_le_frattini {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    (π : FreeGroup α →* G) :
    (Subgroup.closure ({x : FreeGroup α | ∃ a b : FreeGroup α, x = a * b * a⁻¹ * b⁻¹})).map π
      ≤ frattini G := by
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_le (frattini G)).mpr ?_
  rintro x hx
  rw [Set.mem_image] at hx
  rcases hx with ⟨y, ⟨a, b, h⟩, rfl⟩
  rw [h, map_commutator_eq α π a b]
  exact commutator_le_frattini p hG
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top (π a)) (Subgroup.mem_top (π b)))

/-- **Key containment**: the image of `gsPhiF` lies in the Frattini subgroup of a finite
`p`-group, which makes `FreeGroup α ⧸ gsPhiF → G ⧸ frattini G` well defined and surjective.
The `p`-th-power hypothesis `hpow` is `pow_mem_frattini` below. -/
lemma map_gsPhiF_le_frattini {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    (π : FreeGroup α →* G) :
    (gsPhiF p α).map π ≤ frattini G := by
  rw [gsPhiF, MonoidHom.map_closure]
  refine (Subgroup.closure_le (frattini G)).mpr ?_
  rintro x hx
  rw [Set.mem_image] at hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [Set.mem_union] at hy
  rcases hy with ⟨a, b, h⟩ | ⟨g, h⟩
  · rw [h, map_commutator_eq α π a b]
    exact commutator_le_frattini p hG
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top (π a)) (Subgroup.mem_top (π b)))
  · rw [h, map_pow_eq p α π g]
    exact Commons.GroupTheory.PGroup.pow_mem_frattini hG (π g)

/-- The generating set of `gsPhiF` is closed under conjugation, so `gsPhiF` is normal. -/
instance gsPhiF_normal : (gsPhiF p α).Normal := by
  refine Subgroup.Normal.mk (fun n hn g => ?_)
  rw [gsPhiF] at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
      rw [Set.mem_union] at hx
      rcases hx with ⟨a, b, rfl⟩ | ⟨h, rfl⟩
      · refine Subgroup.subset_closure (Or.inl ⟨g * a * g⁻¹, g * b * g⁻¹, ?_⟩)
        group
      · refine Subgroup.subset_closure (Or.inr ⟨MulAut.conj g h, ?_⟩)
        rw [show g * h ^ p * g⁻¹ = MulAut.conj g (h ^ p) by rw [MulAut.conj_apply], map_pow]
  | one => simp
  | mul x y hx hy ihx ihy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ih


end Commons.GroupTheory.ProPGroup

-- ===== end of gsSerre_frattini =====


noncomputable section

namespace Commons.GroupTheory.ProPGroup

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α]

/-- Every element of `FreeGroup α ⧸ gsPhiF` is killed by `p`. -/
lemma pow_eq_one_quot_gsPhiF (x : FreeGroup α ⧸ gsPhiF p α) : x ^ p = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (gsPhiF p α) x
  rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact Subgroup.subset_closure (Or.inr ⟨g, rfl⟩)

/-- The images of the generators generate `FreeGroup α ⧸ gsPhiF` as a group. -/
lemma closure_range_mk_gsPhiF :
    Subgroup.closure (Set.range (fun i : α =>
      QuotientGroup.mk' (gsPhiF p α) (FreeGroup.of i))) = ⊤ := by
  have h := FreeGroup.closure_range_of α
  have hm := congrArg (Subgroup.map (QuotientGroup.mk' (gsPhiF p α))) h
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (gsPhiF p α))] at hm
  have hset : (QuotientGroup.mk' (gsPhiF p α)) '' (Set.range (FreeGroup.of : α → FreeGroup α))
      = Set.range (fun i : α => QuotientGroup.mk' (gsPhiF p α) (FreeGroup.of i)) :=
    (Set.range_comp _ _).symm
  rw [← hm, hset]




/-- **Upper bound** on the order of `FreeGroup α ⧸ gsPhiF`: it is generated by `card α` elements
and killed by `p`, hence a quotient of `(ZMod p) ^ card α`. -/
theorem natCard_quot_gsPhiF_le :
    Nat.card (FreeGroup α ⧸ gsPhiF p α) ≤ p ^ Fintype.card α := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (gsPhiF p α).Normal := gsPhiF_normal p α
  have hcomm : _root_.commutator (FreeGroup α) ≤ gsPhiF p α := by
    rw [show _root_.commutator (FreeGroup α)
        = ⁅(⊤ : Subgroup (FreeGroup α)), ⊤⁆ from rfl]
    refine (Subgroup.commutator_le).mpr (fun a _ b _ => ?_)
    exact Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)
  haveI : IsMulCommutative (FreeGroup α ⧸ gsPhiF p α) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcomm
  letI : CommGroup (FreeGroup α ⧸ gsPhiF p α) :=
    CommGroup.mk (fun a b => IsMulCommutative.is_comm.comm a b)
  have hnsmul : ∀ x : Additive (FreeGroup α ⧸ gsPhiF p α), p • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, pow_eq_one_quot_gsPhiF p α x.toMul, toMul_zero]
  letI : Module (ZMod p) (Additive (FreeGroup α ⧸ gsPhiF p α)) :=
    AddCommGroup.zmodModule (n := p) hnsmul
  let g : α → FreeGroup α ⧸ gsPhiF p α :=
    fun i => QuotientGroup.mk' (gsPhiF p α) (FreeGroup.of i)
  let f : α → Additive (FreeGroup α ⧸ gsPhiF p α) := fun i => Additive.ofMul (g i)
  have hspan_top : Submodule.span (ZMod p) (Set.range f) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x ∈ (Subgroup.closure (Set.range g)).toAddSubgroup := by
      show Additive.toMul x ∈ Subgroup.closure (Set.range g)
      rw [show Subgroup.closure (Set.range g) = ⊤ from closure_range_mk_gsPhiF p α]
      exact Subgroup.mem_top _
    rw [Subgroup.toAddSubgroup_closure] at hx
    refine (AddSubgroup.closure_le ((Submodule.span (ZMod p) (Set.range f)).toAddSubgroup)).mpr ?_ hx
    intro y hy
    obtain ⟨i, hi⟩ := hy
    have hyf : y = f i := by
      apply Additive.toMul.injective
      simpa [f, g] using hi.symm
    rw [hyf]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hsurj : Function.Surjective (Finsupp.linearCombination (ZMod p) f) := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hspan_top]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    exact ⟨Finsupp.single i 1, by simp [f, g]⟩
  calc Nat.card (FreeGroup α ⧸ gsPhiF p α)
      = Nat.card (Additive (FreeGroup α ⧸ gsPhiF p α)) :=
        (Nat.card_congr Additive.toMul).symm
    _ ≤ Nat.card (α →₀ ZMod p) := Nat.card_le_card_of_surjective _ hsurj
    _ = p ^ Fintype.card α := by
        rw [Nat.card_eq_fintype_card, Fintype.card_finsupp, ZMod.card]


/-- **Finiteness** of `FreeGroup α ⧸ gsPhiF`: same quotient-of-`(α →₀ ZMod p)` argument,
exposing the `Finite` instance. -/
lemma finite_quot_gsPhiF : Finite (FreeGroup α ⧸ gsPhiF p α) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (gsPhiF p α).Normal := gsPhiF_normal p α
  have hcomm : _root_.commutator (FreeGroup α) ≤ gsPhiF p α := by
    rw [show _root_.commutator (FreeGroup α)
        = ⁅(⊤ : Subgroup (FreeGroup α)), ⊤⁆ from rfl]
    refine (Subgroup.commutator_le).mpr (fun a _ b _ => ?_)
    exact Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)
  haveI : IsMulCommutative (FreeGroup α ⧸ gsPhiF p α) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcomm
  letI : CommGroup (FreeGroup α ⧸ gsPhiF p α) :=
    CommGroup.mk (fun a b => IsMulCommutative.is_comm.comm a b)
  have hnsmul : ∀ x : Additive (FreeGroup α ⧸ gsPhiF p α), p • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, pow_eq_one_quot_gsPhiF p α x.toMul, toMul_zero]
  letI : Module (ZMod p) (Additive (FreeGroup α ⧸ gsPhiF p α)) :=
    AddCommGroup.zmodModule (n := p) hnsmul
  let g : α → FreeGroup α ⧸ gsPhiF p α :=
    fun i => QuotientGroup.mk' (gsPhiF p α) (FreeGroup.of i)
  let f : α → Additive (FreeGroup α ⧸ gsPhiF p α) := fun i => Additive.ofMul (g i)
  have hspan_top : Submodule.span (ZMod p) (Set.range f) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x ∈ (Subgroup.closure (Set.range g)).toAddSubgroup := by
      show Additive.toMul x ∈ Subgroup.closure (Set.range g)
      rw [show Subgroup.closure (Set.range g) = ⊤ from closure_range_mk_gsPhiF p α]
      exact Subgroup.mem_top _
    rw [Subgroup.toAddSubgroup_closure] at hx
    refine (AddSubgroup.closure_le ((Submodule.span (ZMod p) (Set.range f)).toAddSubgroup)).mpr ?_ hx
    intro y hy
    obtain ⟨i, hi⟩ := hy
    have hyf : y = f i := by
      apply Additive.toMul.injective
      simpa [f, g] using hi.symm
    rw [hyf]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hsurj : Function.Surjective (Finsupp.linearCombination (ZMod p) f) := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hspan_top]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    exact ⟨Finsupp.single i 1, by simp [f, g]⟩
  haveI hfin : Finite (Additive (FreeGroup α ⧸ gsPhiF p α)) := Finite.of_surjective _ hsurj
  exact (Additive.toMul.symm.finite_iff).mpr hfin


end Commons.GroupTheory.ProPGroup

-- ===== end of gsSerre_bound =====


noncomputable section

namespace Commons.GroupTheory.ProPGroup

variable (p : ℕ) [Fact p.Prime]

/-- **Burnside basis, packaged.**  For a finite `p`-group the Frattini quotient has order `p ^ d`
where `d` is the minimal number of generators, and there is a minimal generating `Finset` of
cardinality `d`. -/
theorem natCard_quotient_frattini_eq_pow_minGen
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) :
    ∃ (d : ℕ) (S : Finset G), Nat.card (G ⧸ frattini G) = p ^ d ∧ S.card = d ∧
      Subgroup.closure (S : Set G) = ⊤ ∧ ∀ T : Finset G, Subgroup.closure (T : Set G) = ⊤ → d ≤ T.card := by
  classical
  obtain ⟨S, hcard, hgen, hmin⟩ := Commons.GroupTheory.PGroup.burnside_basis (p := p) hG
  exact ⟨S.card, S, hcard, rfl, hgen, hmin⟩

/-- **The first quotient order.**  If `π : FreeGroup α ↠ G` is surjective with `card α` minimal
among generating sets of the finite `p`-group `G`, then `G ⧸ frattini G` has order `p ^ card α`. -/
theorem natCard_quotient_frattini_eq_pow_card
    {α G : Type*} [Fintype α] [Group G] [Finite G] (hG : IsPGroup p G)
    (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) :
    Nat.card (G ⧸ frattini G) = p ^ Fintype.card α := by
  classical
  obtain ⟨S, hcard, hgenS, hmin⟩ := Commons.GroupTheory.PGroup.burnside_basis (p := p) hG
  have hgenT : Subgroup.closure
      ((Finset.univ.image (fun i : α => π (FreeGroup.of i)) : Finset G) : Set G) = ⊤ := by
    have hTset : ((Finset.univ.image (fun i : α => π (FreeGroup.of i)) : Finset G) : Set G)
        = Set.range (fun i : α => π (FreeGroup.of i)) := by
      simp [Set.range]
    have hrange : Set.range (fun i : α => π (FreeGroup.of i))
        = π '' (Set.range (FreeGroup.of : α → FreeGroup α)) := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨FreeGroup.of i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hTset, hrange, ← MonoidHom.map_closure, FreeGroup.closure_range_of α,
      Subgroup.map_top_of_surjective π hπ]
  have hSle : S.card ≤ Fintype.card α := by
    have h1 : S.card ≤ (Finset.univ.image (fun i : α => π (FreeGroup.of i)) : Finset G).card :=
      hmin _ hgenT
    have h2 : (Finset.univ.image (fun i : α => π (FreeGroup.of i)) : Finset G).card
        ≤ (Finset.univ : Finset α).card := Finset.card_image_le
    rw [Finset.card_univ] at h2
    exact le_trans h1 h2
  have hcardα : Fintype.card α ≤ S.card := hgen S hgenS
  rw [hcard, le_antisymm hSle hcardα]





/-- **The kernel of a minimal surjection lies in the Frattini-like subgroup of the free group.**
`FreeGroup α ⧸ gsPhiF` and `G ⧸ frattini G` both have order `p ^ card α` and the latter is a
quotient of the former, so that quotient map is an isomorphism. -/
theorem ker_le_gsPhiF
    {α G : Type*} [Fintype α] [Group G] [Finite G] (hG : IsPGroup p G)
    (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) :
    π.ker ≤ gsPhiF p α := by
  classical
  haveI : (gsPhiF p α).Normal := gsPhiF_normal p α
  haveI : Finite (FreeGroup α ⧸ gsPhiF p α) := finite_quot_gsPhiF p α
  have hle' : (gsPhiF p α) ≤ Subgroup.comap π (frattini G) :=
    (Subgroup.map_le_iff_le_comap).mp (map_gsPhiF_le_frattini p α hG π)
  let q : FreeGroup α ⧸ gsPhiF p α →* G ⧸ frattini G :=
    QuotientGroup.map (gsPhiF p α) (frattini G) π hle'
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) y
    obtain ⟨z, rfl⟩ := hπ x
    exact ⟨QuotientGroup.mk' (gsPhiF p α) z, QuotientGroup.map_mk' _ _ _ _ _⟩
  have hcard : Nat.card (G ⧸ frattini G) = p ^ Fintype.card α :=
    natCard_quotient_frattini_eq_pow_card p hG π hπ hgen
  have heq : Nat.card (FreeGroup α ⧸ gsPhiF p α) = p ^ Fintype.card α :=
    le_antisymm (natCard_quot_gsPhiF_le p α) (hcard ▸ Nat.card_le_card_of_surjective q hq)
  have hker1 : Nat.card q.ker = 1 := by
    have h1 : Nat.card ((FreeGroup α ⧸ gsPhiF p α) ⧸ q.ker) = Nat.card (G ⧸ frattini G) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv
    have hLag := Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker
    rw [heq] at hLag
    rw [h1, hcard] at hLag
    have key : p ^ Fintype.card α * Nat.card q.ker = p ^ Fintype.card α * 1 := by
      rw [mul_one]; exact hLag.symm
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos _) key
  haveI : Subsingleton q.ker := (Nat.card_eq_one_iff_unique.mp hker1).1
  have hker : q.ker = ⊥ := Subgroup.eq_bot_of_subsingleton _
  intro x hx
  have h1 : q (QuotientGroup.mk' (gsPhiF p α) x) = 1 := by
    rw [QuotientGroup.map_mk', MonoidHom.mem_ker.mp hx]
    simp
  have h2 : QuotientGroup.mk' (gsPhiF p α) x ∈ q.ker := (MonoidHom.mem_ker (f := q)).mpr h1
  rw [hker] at h2
  have h3 : QuotientGroup.mk' (gsPhiF p α) x = 1 := by simpa using h2
  exact (QuotientGroup.eq_one_iff (x := x)).mp h3

/-- **Relators of any element of `π.ker` lie in the square of the augmentation ideal.**  This is
step (β): the kernel of the presentation map consists of "order ≥ 2" elements. -/
theorem sub_one_mem_gsIW_sq_of_mem_ker
    {α G : Type*} [Fintype α] [Group G] [Finite G] (hG : IsPGroup p G)
    (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {n : FreeGroup α} (hn : n ∈ π.ker) :
    MonoidAlgebra.of (ZMod p) (FreeGroup α) n - 1 ∈ gsIW p α ^ 2 := by
  refine sub_one_mem_gsIW_sq_of_le_gsPhi p α ?_ hn
  rw [show gsPhi p α = gsPhiF p α from rfl]
  exact ker_le_gsPhiF p hG π hπ hgen

end Commons.GroupTheory.ProPGroup



-- ===== end of gsSerre_count =====


noncomputable section

namespace Commons.GroupTheory.ProPGroup

open MonoidAlgebra

universe u

variable (p : ℕ) [Fact p.Prime]

/-- The augmentation `F_p[G] → F_p` of the group algebra of `G`. -/
def augG (G : Type*) [Group G] : MonoidAlgebra (ZMod p) G →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) G (1 : G →* ZMod p)

/-- The augmentation ideal of `F_p[G]`. -/
def augIdealG (G : Type*) [Group G] : Ideal (MonoidAlgebra (ZMod p) G) :=
  RingHom.ker (augG p G).toRingHom

lemma mem_augIdealG_iff {G : Type*} [Group G] (c : MonoidAlgebra (ZMod p) G) :
    c ∈ augIdealG p G ↔ augG p G c = 0 := Iff.rfl

variable {G : Type*} [Group G] [Fintype G]

lemma augG_of (g : G) : augG p G (MonoidAlgebra.of (ZMod p) G g) = 1 :=
  MonoidAlgebra.lift_of _ g

/-- The augmentation as a sum of coefficients. -/
lemma augG_eq_sum_coeff (c : MonoidAlgebra (ZMod p) G) :
    augG p G c = c.coeff.sum (fun _ a => a) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single (f := c)]
  rw [Finsupp.sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [augG, MonoidAlgebra.lift_single]

lemma sub_algebraMap_augG_mem (c : MonoidAlgebra (ZMod p) G) :
    c - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augG p G c) ∈ augIdealG p G := by
  rw [mem_augIdealG_iff, map_sub, AlgHom.commutes]
  simp

variable {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
  [Module (MonoidAlgebra (ZMod p) G) V] [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) V]

lemma single_eq_smul_of (g : G) (a : ZMod p) :
    (MonoidAlgebra.single g a : MonoidAlgebra (ZMod p) G) = a • MonoidAlgebra.of (ZMod p) G g := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Rewriting an element of the group algebra as its coefficient expansion. -/
lemma sum_coeff_smul (x : V) (z : MonoidAlgebra (ZMod p) G) :
    z • x = z.coeff.sum (fun g a => a • (MonoidAlgebra.of (ZMod p) G g • x)) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single (f := z)]
  simp only [Finsupp.sum]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [single_eq_smul_of p g, smul_assoc]

/-- **Key computation**: if `x` is fixed by the group, the whole group algebra acts through the
augmentation. -/
lemma smul_eq_aug_smul {x : V}
    (hx : ∀ g : G, MonoidAlgebra.of (ZMod p) G g • x = x)
    (z : MonoidAlgebra (ZMod p) G) : z • x = augG p G z • x := by
  rw [sum_coeff_smul p x z]
  have h1 : z.coeff.sum (fun g a => a • (MonoidAlgebra.of (ZMod p) G g • x))
      = z.coeff.sum (fun _ a => a • x) := by
    refine Finsupp.sum_congr fun g _ => ?_
    rw [hx g]
  rw [h1]
  have h2 : z.coeff.sum (fun _ a => a • x) = (z.coeff.sum (fun _ a => a)) • x := by
    simp only [Finsupp.sum]
    rw [Finset.sum_smul]
  rw [h2, ← augG_eq_sum_coeff p z]

lemma smul_eq_zero_of_mem_augIdealG {x : V}
    (hx : ∀ g : G, MonoidAlgebra.of (ZMod p) G g • x = x)
    {z : MonoidAlgebra (ZMod p) G} (hz : z ∈ augIdealG p G) : z • x = 0 := by
  rw [smul_eq_aug_smul p hx z, (mem_augIdealG_iff p z).mp hz, zero_smul]

/-- In a finite module over `F_p` carrying an action of the finite `p`-group `G`, there is a
nonzero fixed vector. -/
lemma exists_ne_zero_fixed_of_isPGroup (hG : IsPGroup p G) {V : Type u} [AddCommGroup V]
    [Module (ZMod p) V] [Nontrivial V] [Finite V] [MulAction G V]
    (h0 : (0 : V) ∈ MulAction.fixedPoints G V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, g • v = v := by
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfr : 0 < Module.finrank (ZMod p) V := Module.finrank_pos
  have hcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints G V) := by
    have h1 : p ∣ Nat.card V := by
      rw [hcard]
      exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hfr)
    exact (Nat.ModEq.dvd_iff (IsPGroup.card_modEq_card_fixedPoints hG V) (dvd_refl p)).mp h1
  have hne : Nat.card (MulAction.fixedPoints G V) ≠ 1 := by
    intro h1
    rw [h1] at hdvd
    exact (Fact.out : p.Prime).not_dvd_one hdvd
  have htwo : 2 ≤ Nat.card (MulAction.fixedPoints G V) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints G V) :=
      Nat.card_pos_iff.mpr ⟨⟨0, h0⟩, inferInstance⟩
    omega
  have hne0 : ∃ v : V, v ∈ MulAction.fixedPoints G V ∧ v ≠ 0 := by
    by_contra hcon
    have hsub : MulAction.fixedPoints G V ⊆ {0} := by
      intro v hv
      rw [Set.mem_singleton_iff]
      by_contra hv0
      exact hcon ⟨v, hv, hv0⟩
    haveI : Subsingleton ↥(MulAction.fixedPoints G V) :=
      ⟨fun a b => Subtype.ext (by
        have ha := hsub a.2
        have hb := hsub b.2
        rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb])⟩
    haveI : Nonempty ↥(MulAction.fixedPoints G V) := ⟨⟨0, h0⟩⟩
    have hle : Nat.card (MulAction.fixedPoints G V) ≤ 1 := by
      rw [Nat.card_unique]
    omega
  obtain ⟨v, hv, hv0⟩ := hne0
  exact ⟨v, hv0, fun g => (MulAction.mem_fixedPoints).mp hv g⟩


instance augIdealG_isTwoSided : (augIdealG p G).IsTwoSided :=
  Ideal.IsTwoSided.mk fun b ha => by
    rw [mem_augIdealG_iff, map_mul, (mem_augIdealG_iff p _).mp ha, zero_mul]

section Aux

variable {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
  [Module (MonoidAlgebra (ZMod p) G) V] [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) V]

/-- The image of `augIdealG • ⊤` under a quotient map. -/
lemma mkQ_mem_smul_top (N : Submodule (MonoidAlgebra (ZMod p) G) V) {y : V}
    (hy : y ∈ augIdealG p G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) V)) :
    N.mkQ y ∈ augIdealG p G •
      (⊤ : Submodule (MonoidAlgebra (ZMod p) G) (V ⧸ N)) :=
  Submodule.smul_induction_on
    (p := fun y => N.mkQ y ∈ augIdealG p G •
      (⊤ : Submodule (MonoidAlgebra (ZMod p) G) (V ⧸ N))) hy
    (fun r hr n _ => by
      rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top)
    (fun a b _ _ => by
      rw [map_add]
      exact Submodule.add_mem _ ‹_› ‹_›)

end Aux

section Aux2

variable {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
  [Module (MonoidAlgebra (ZMod p) G) V] [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) V]

/-- A nonzero finite module has a maximal proper submodule. -/
lemma exists_isCoatom_of_nontrivial [Finite V] [Nontrivial V] :
    ∃ N : Submodule (MonoidAlgebra (ZMod p) G) V, IsCoatom N := by
  classical
  haveI : Finite (Submodule (MonoidAlgebra (ZMod p) G) V) := inferInstance
  haveI : Nontrivial (Submodule (MonoidAlgebra (ZMod p) G) V) := inferInstance
  have hfin : ({p : Submodule (MonoidAlgebra (ZMod p) G) V | p ≠ ⊤} : Set _).Finite :=
    Set.toFinite _
  have hne : ({p : Submodule (MonoidAlgebra (ZMod p) G) V | p ≠ ⊤} : Set _).Nonempty :=
    ⟨⊥, bot_ne_top⟩
  obtain ⟨N, hNmax⟩ := Set.Finite.exists_maximal hfin hne
  refine ⟨N, hNmax.1, ?_⟩
  intro c hc
  rcases eq_or_ne c ⊤ with h | h
  · exact h
  · exact absurd (le_antisymm hc.le (hNmax.2 h hc.le)).symm (ne_of_gt hc)

/-- Every simple finite module over the group algebra of a finite `p`-group is killed by the
augmentation ideal. -/
lemma smul_eq_bot_of_isSimpleModule (hG : IsPGroup p G) [Finite V] [Nontrivial V]
    [IsSimpleModule (MonoidAlgebra (ZMod p) G) V] :
    augIdealG p G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) V) = ⊥ := by
  letI : MulAction G V := MulAction.compHom V (MonoidAlgebra.of (ZMod p) G)
  have hfix0 : (0 : V) ∈ MulAction.fixedPoints G V := by
    rw [MulAction.mem_fixedPoints]
    intro g
    show MonoidAlgebra.of (ZMod p) G g • (0 : V) = 0
    exact smul_zero _
  obtain ⟨x, hx0, hxfixed⟩ := exists_ne_zero_fixed_of_isPGroup p hG hfix0
  have hxsmul : ∀ g : G, MonoidAlgebra.of (ZMod p) G g • x = x := fun g => hxfixed g
  have htop : (⊤ : Submodule (MonoidAlgebra (ZMod p) G) V) =
      Submodule.span (MonoidAlgebra (ZMod p) G) {x} :=
    (IsSimpleModule.span_singleton_eq_top (MonoidAlgebra (ZMod p) G) hx0).symm
  rw [htop, Submodule.eq_bot_iff]
  intro y hy
  refine Submodule.smul_induction_on (p := fun y => y = 0) hy ?_ ?_
  · intro r hr m hm
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [← smul_assoc]
    exact smul_eq_zero_of_mem_augIdealG p hxsmul
      (Ideal.mul_mem_right (I := augIdealG p G) c hr)
  · intro a b ha hb
    rw [ha, hb, add_zero]

/-- **Nakayama-type statement**: a nontrivial finite module over the group algebra of a finite
`p`-group is not generated by `augIdealG`. -/
theorem smul_ne_top (hG : IsPGroup p G) [Finite V] [Nontrivial V] :
    augIdealG p G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) V) ≠ ⊤ := by
  intro htop
  obtain ⟨N, hN⟩ := exists_isCoatom_of_nontrivial (p := p) (G := G) (V := V)
  haveI : IsSimpleModule (MonoidAlgebra (ZMod p) G) (V ⧸ N) :=
    isSimpleModule_iff_isCoatom.mpr hN
  haveI : Nontrivial (V ⧸ N) := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) G) (V ⧸ N)
  haveI : Finite (V ⧸ N) := Finite.of_surjective N.mkQ N.mkQ_surjective
  have htop' : augIdealG p G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) (V ⧸ N)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨v, rfl⟩ := N.mkQ_surjective y
    exact mkQ_mem_smul_top p N (htop.ge Submodule.mem_top)
  have hbot := smul_eq_bot_of_isSimpleModule (p := p) (G := G) hG (V := V ⧸ N)
  rw [hbot] at htop'
  exact bot_ne_top htop'

end Aux2

section Aux3

open MonoidAlgebra in
/-- If `I * M = M` for an ideal `M`, then `I` generates the whole module `↥M`. -/
lemma smul_top_eq_top_of_mul_eq {M : Ideal (MonoidAlgebra (ZMod p) G)}
    (h : augIdealG p G * M = M) :
    augIdealG p G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) ↥M) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro m
  have hle : augIdealG p G * M ≤
      Submodule.map M.subtype (augIdealG p G •
        (⊤ : Submodule (MonoidAlgebra (ZMod p) G) ↥M)) := by
    rw [Ideal.mul_le]
    intro a ha b hb
    exact Submodule.mem_map.mpr ⟨a • (⟨b, hb⟩ : ↥M),
      Submodule.smul_mem_smul ha Submodule.mem_top, rfl⟩
  have hm : (m : MonoidAlgebra (ZMod p) G) ∈ augIdealG p G * M := by
    rw [h]
    exact m.2
  obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.mp (hle hm)
  have : y = m := Subtype.ext hyeq
  rwa [this] at hy

end Aux3

/-- **The augmentation ideal of the group algebra of a finite `p`-group is nilpotent.** -/
theorem isNilpotent_augIdealG (hG : IsPGroup p G) : IsNilpotent (augIdealG p G) := by
  classical
  haveI : Finite (MonoidAlgebra (ZMod p) G) := by
    refine Finite.of_injective (β := G → ZMod p)
      (fun f : MonoidAlgebra (ZMod p) G => fun g => f.coeff g) ?_
    intro a b h
    ext g
    exact congrFun h g
  have hex : ∃ N, (augIdealG p G) ^ (N + 1) = (augIdealG p G) ^ N := by
    by_contra h
    push_neg at h
    have hstrict : ∀ k, (augIdealG p G) ^ (k + 1) < (augIdealG p G) ^ k := by
      intro k
      exact lt_of_le_of_ne (Ideal.pow_le_pow_right (Nat.le_succ k)) (h k)
    have hinj : Function.Injective (fun k : ℕ => (augIdealG p G) ^ k) := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 : (augIdealG p G) ^ b ≤ (augIdealG p G) ^ (a + 1) :=
          Ideal.pow_le_pow_right hlt
        exact absurd hab.symm (ne_of_lt (lt_of_le_of_lt h1 (hstrict a)))
      · have h1 : (augIdealG p G) ^ a ≤ (augIdealG p G) ^ (b + 1) :=
          Ideal.pow_le_pow_right hgt
        exact absurd hab (ne_of_lt (lt_of_le_of_lt h1 (hstrict b)))
    exact (not_finite_iff_infinite.mpr (inferInstance : Infinite ℕ))
      (Finite.of_injective _ hinj)
  obtain ⟨N, hN⟩ := hex
  by_cases hbot : (augIdealG p G) ^ N = ⊥
  · exact ⟨N, hbot⟩
  · exfalso
    haveI : Nontrivial ↥((augIdealG p G) ^ N) := Submodule.nontrivial_iff_ne_bot.mpr hbot
    have hmul : augIdealG p G * (augIdealG p G) ^ N = (augIdealG p G) ^ N := by
      rcases Nat.eq_zero_or_pos N with hzero | hpos
      · subst hzero
        have hI : augIdealG p G = ⊤ := by
          simpa [Submodule.pow_zero, Submodule.pow_one] using hN
        rw [hI, Submodule.pow_zero, Ideal.top_mul]
      · rw [← Submodule.pow_succ' (augIdealG p G) (Nat.pos_iff_ne_zero.mp hpos)]
        exact hN
    have htop := smul_top_eq_top_of_mul_eq p hmul
    exact smul_ne_top (p := p) (G := G) hG htop

end Commons.GroupTheory.ProPGroup

-- ===== end of gsSerre_nilp =====


noncomputable section
open MonoidAlgebra

namespace ScratchGS

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]

abbrev W := MonoidAlgebra (ZMod p) (FreeGroup α)

/-- `of x_i` if `b = true`, `of (x_i)⁻¹` if `b = false`. -/
def ofLetter (c : α × Bool) : W p α :=
  match c with
  | (a, true) => MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of a)
  | (a, false) => MonoidAlgebra.of (ZMod p) (FreeGroup α) ((FreeGroup.of a)⁻¹)

def ofWord (L : List (α × Bool)) : W p α := (L.map (ofLetter p α)).prod

lemma ofLetter_mul_inv (x : α) :
    ofLetter p α (x, true) * ofLetter p α (x, false) = 1 := by
  simp only [ofLetter]
  rw [← map_mul]
  simp [MonoidAlgebra.one_def]

lemma ofLetter_mul_not (x : α) (b : Bool) :
    ofLetter p α (x, b) * ofLetter p α (x, !b) = 1 := by
  cases b with
  | true => simpa using ofLetter_mul_inv p α x
  | false =>
      have h : ofLetter p α (x, false) * ofLetter p α (x, true) = 1 := by
        simp only [ofLetter]
        rw [← map_mul]
        simp [MonoidAlgebra.one_def]
      simpa using h

lemma ofWord_append (L M : List (α × Bool)) :
    ofWord p α (L ++ M) = ofWord p α L * ofWord p α M := by
  simp only [ofWord, List.map_append, List.prod_append]

/-- the "letter derivative" `D_i(x_i) = 1`, `D_i(x_i⁻¹) = -of x_i⁻¹`, `D_i(x_j)=0` for `j≠i`. -/
def dLetter (i : α) (c : α × Bool) : W p α :=
  if c.1 = i then
    (match c.2 with | true => 1 | false => -(ofLetter p α (c.1, false)))
  else 0

/-- `D_i` on a raw word, left-to-right. -/
def Dlist (i : α) : List (α × Bool) → W p α
  | [] => 0
  | c :: t => dLetter p α i c + ofLetter p α c * Dlist i t

lemma Dlist_append (i : α) (L M : List (α × Bool)) :
    Dlist p α i (L ++ M) = Dlist p α i L + ofWord p α L * Dlist p α i M := by
  induction L with
  | nil => simp [Dlist, ofWord]
  | cons c t ih =>
      simp only [List.cons_append, Dlist]
      rw [ih]
      simp only [ofWord, List.map_cons, List.prod_cons]
      rw [mul_add, mul_assoc]
      abel

lemma dLetter_cancel (i x : α) (b : Bool) (Y : W p α) :
    dLetter p α i (x, b) + ofLetter p α (x, b) *
      (dLetter p α i (x, !b) + ofLetter p α (x, !b) * Y) = Y := by
  have hkey : dLetter p α i (x, b) + ofLetter p α (x, b) * dLetter p α i (x, !b) = 0 := by
    cases b with
    | false =>
        by_cases hx : x = i
        · subst hx
          simp only [Bool.not_false, dLetter, ofLetter, if_true]
          simp
        · simp [dLetter, ofLetter, hx]
    | true =>
        by_cases hx : x = i
        · subst hx
          simp only [Bool.not_true, dLetter, ofLetter, if_true]
          rw [mul_neg, ← map_mul, mul_inv_cancel, map_one, MonoidAlgebra.one_def, add_neg_cancel]
        · simp [dLetter, ofLetter, hx]
  rw [mul_add, ← add_assoc, hkey, zero_add, ← mul_assoc, ofLetter_mul_not p α x b, one_mul]

lemma Dlist_reduce_step (i : α) (L₁ L₂ : List (α × Bool)) (x : α) (b : Bool) :
    Dlist p α i (L₁ ++ (x, b) :: (x, !b) :: L₂) = Dlist p α i (L₁ ++ L₂) := by
  rw [Dlist_append, Dlist_append]
  simp only [Dlist]
  rw [dLetter_cancel p α i x b (Dlist p α i L₂)]

/-- the Fox derivative on the free group. -/
def Dfun (i : α) : FreeGroup α → W p α :=
  Quot.lift (Dlist p α i) (fun a b h => by
    cases h with
    | not => exact Dlist_reduce_step p α i _ _ _ _)

lemma ofLetter_eq_mk (c : α × Bool) :
    ofLetter p α c = MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.mk [c]) := by
  obtain ⟨a, b⟩ := c
  cases b <;> rfl

lemma ofWord_mk (L : List (α × Bool)) :
    ofWord p α L = MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.mk L) := by
  induction L with
  | nil => rw [ofWord, List.map_nil, List.prod_nil,
      show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl, map_one, MonoidAlgebra.one_def]
  | cons c t ih =>
      change ofLetter p α c * ofWord p α t =
        MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.mk (c :: t))
      rw [ih, ofLetter_eq_mk p α c, ← map_mul, FreeGroup.mul_mk]
      rfl

lemma Dfun_mul (i : α) (g h : FreeGroup α) :
    Dfun p α i (g * h) =
      Dfun p α i g + MonoidAlgebra.of (ZMod p) (FreeGroup α) g * Dfun p α i h := by
  have hgh : g * h = FreeGroup.mk (g.toWord ++ h.toWord) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := g), ← FreeGroup.mk_toWord (x := h),
      FreeGroup.mul_mk]
  rw [hgh]
  have e1 : Dfun p α i (FreeGroup.mk (g.toWord ++ h.toWord))
      = Dlist p α i (g.toWord ++ h.toWord) := rfl
  rw [e1, Dlist_append]
  have e2 : Dfun p α i g = Dlist p α i g.toWord := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := g)]
    rfl
  have e3 : ofWord p α g.toWord = MonoidAlgebra.of (ZMod p) (FreeGroup α) g := by
    rw [ofWord_mk, FreeGroup.mk_toWord]
  have e4 : Dfun p α i h = Dlist p α i h.toWord := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := h)]
    rfl
  rw [e2, e3, e4]

/-- the linear extension of the Fox derivative to the whole group algebra. -/
def Dlin (i : α) : W p α →ₗ[ZMod p] W p α where
  toFun x := (Finsupp.linearCombination (ZMod p) (Dfun p α i)) x.coeff
  map_add' x y := by
    rw [MonoidAlgebra.coeff_add, map_add]
  map_smul' c x := by
    rw [MonoidAlgebra.coeff_smul, map_smul, RingHom.id_apply]

lemma Dlin_apply (i : α) (x : W p α) :
    Dlin p α i x = (Finsupp.linearCombination (ZMod p) (Dfun p α i)) x.coeff := rfl

lemma Dlin_of (i : α) (g : FreeGroup α) :
    Dlin p α i (MonoidAlgebra.of (ZMod p) (FreeGroup α) g) = Dfun p α i g := by
  rw [Dlin_apply, MonoidAlgebra.of_apply]
  have h1 : (MonoidAlgebra.single g (1 : ZMod p)).coeff = Finsupp.single g 1 := rfl
  rw [h1, Finsupp.linearCombination_single, one_smul]

lemma Dlin_mul_of (i : α) (x : W p α) (g : FreeGroup α) :
    Dlin p α i (x * MonoidAlgebra.of (ZMod p) (FreeGroup α) g) =
      Dlin p α i x + x * Dlin p α i (MonoidAlgebra.of (ZMod p) (FreeGroup α) g) := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      rw [Dlin_of, Dlin_of]
      have h1 : MonoidAlgebra.of (ZMod p) (FreeGroup α) m *
          MonoidAlgebra.of (ZMod p) (FreeGroup α) g
          = MonoidAlgebra.of (ZMod p) (FreeGroup α) (m * g) := by rw [map_mul]
      rw [h1, Dlin_of, Dfun_mul]
  | add x y hx hy =>
      have h1 : Dlin p α i ((x + y) * MonoidAlgebra.of (ZMod p) (FreeGroup α) g)
          = Dlin p α i (x * MonoidAlgebra.of (ZMod p) (FreeGroup α) g)
            + Dlin p α i (y * MonoidAlgebra.of (ZMod p) (FreeGroup α) g) := by
        rw [add_mul, map_add]
      rw [h1, hx, hy]
      conv_rhs => rw [map_add, add_mul]
      abel
  | smul r x hx =>
      simp only [smul_mul_assoc, map_smul, hx, smul_add]

lemma Dfun_of (i j : α) : Dfun p α i (FreeGroup.of j) = if j = i then 1 else 0 := by
  have h1 : FreeGroup.of j = FreeGroup.mk [(j, true)] := rfl
  rw [h1]
  have h2 : Dfun p α i (FreeGroup.mk [(j, true)]) = Dlist p α i [(j, true)] := rfl
  rw [h2]
  have h3 : Dlist p α i [(j, true)]
      = dLetter p α i (j, true) + ofLetter p α (j, true) * Dlist p α i ([] : List (α × Bool)) := rfl
  rw [h3, show Dlist p α i ([] : List (α × Bool)) = 0 from rfl, mul_zero, add_zero]
  by_cases h : j = i
  · simp [dLetter, h]
  · simp [dLetter, h]

/-- the augmentation `W →ₐ ZMod p`. -/
noncomputable def aug : W p α →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) (FreeGroup α) (1 : FreeGroup α →* ZMod p)

lemma aug_of (g : FreeGroup α) :
    aug p α (MonoidAlgebra.of (ZMod p) (FreeGroup α) g) = 1 := by
  simp [aug]

lemma aug_one : aug p α (1 : W p α) = 1 := by
  rw [← map_one (MonoidAlgebra.of (ZMod p) (FreeGroup α)), aug_of]

/-- the augmentation ideal of `W`. -/
def IW : Ideal (W p α) := RingHom.ker (aug p α).toRingHom

lemma mem_IW_iff (z : W p α) : z ∈ IW p α ↔ aug p α z = 0 := Iff.rfl

/-- the generators `t_i = of x_i - 1` of the augmentation ideal. -/
def t (i : α) : W p α := MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of i) - 1

lemma aug_t (i : α) : aug p α (t p α i) = 0 := by
  rw [t, map_sub, aug_of, map_one, sub_self]

/-- the left `W`-linear map `W^α → IW`. -/
def Psi (q : α → W p α) : W p α := ∑ i : α, q i * t p α i

/-- its inverse on `IW`, given by the Fox derivatives. -/
def PsiInv (z : W p α) : α → W p α := fun i => Dlin p α i z

lemma Dlin_one (i : α) : Dlin p α i (1 : W p α) = 0 := by
  show Dlin p α i (MonoidAlgebra.of (ZMod p) (FreeGroup α) 1) = 0
  rw [Dlin_of]
  rfl

lemma Psi_mem_IW (q : α → W p α) : Psi p α q ∈ IW p α := by
  rw [mem_IW_iff, Psi, map_sum]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [map_mul, aug_t, mul_zero]

lemma Dlin_t (i j : α) : Dlin p α i (t p α j) = if j = i then 1 else 0 := by
  rw [t, map_sub, Dlin_of, Dfun_of, Dlin_one, sub_zero]

lemma Dlin_mul_t (i j : α) (x : W p α) :
    Dlin p α i (x * t p α j) = x * (if j = i then 1 else 0) := by
  rw [t, mul_sub, mul_one, map_sub, Dlin_mul_of, Dlin_of, Dfun_of]
  abel

lemma PsiInv_Psi (q : α → W p α) : PsiInv p α (Psi p α q) = q := by
  funext i
  show Dlin p α i (∑ j : α, q j * t p α j) = q i
  rw [map_sum]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [Dlin_mul_t, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Dlin_mul_t, if_neg hj, mul_zero]

def F (g : FreeGroup α) : W p α := ∑ i : α, Dfun p α i g * t p α i

lemma F_one : F p α 1 = 0 := by
  simp only [F]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [show Dfun p α i 1 = 0 from rfl, zero_mul]

lemma F_of (j : α) : F p α (FreeGroup.of j) = t p α j := by
  rw [F]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [Dfun_of, if_pos rfl, one_mul]
  · intro i _ hi
    rw [Dfun_of, if_neg (Ne.symm hi), zero_mul]

lemma F_mul (g h : FreeGroup α) :
    F p α (g * h) = F p α g + MonoidAlgebra.of (ZMod p) (FreeGroup α) g * F p α h := by
  rw [F, F, F, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Dfun_mul, add_mul, mul_assoc]

lemma fox_group (g : FreeGroup α) :
    F p α g = MonoidAlgebra.of (ZMod p) (FreeGroup α) g - 1 := by
  induction g using FreeGroup.induction_on with
  | one => rw [F_one, map_one, MonoidAlgebra.one_def, sub_self]
  | of j => rw [F_of, t]
  | inv_of j _ =>
      have h3 : F p α ((FreeGroup.of j)⁻¹)
          = MonoidAlgebra.of (ZMod p) (FreeGroup α) ((FreeGroup.of j)⁻¹) - 1 := by
        have hmul := F_mul p α (FreeGroup.of j) ((FreeGroup.of j)⁻¹)
        rw [mul_inv_cancel, F_one, F_of p α j] at hmul
        have key : MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of j) *
            F p α ((FreeGroup.of j)⁻¹)
            = 1 - MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of j) := by
          have hsum : MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of j) *
              F p α ((FreeGroup.of j)⁻¹)
              + (MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of j) - 1) = 0 := by
            rw [t] at hmul
            exact (add_comm _ _).trans hmul.symm
          rw [add_eq_zero_iff_eq_neg] at hsum
          rw [hsum, neg_sub]
        have hmm : MonoidAlgebra.of (ZMod p) (FreeGroup α) ((FreeGroup.of j)⁻¹) *
            MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of j) = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one, MonoidAlgebra.one_def]
        calc F p α ((FreeGroup.of j)⁻¹)
            = MonoidAlgebra.of (ZMod p) (FreeGroup α) ((FreeGroup.of j)⁻¹) *
              (MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of j) *
                F p α ((FreeGroup.of j)⁻¹)) := by
                rw [← mul_assoc, hmm, one_mul]
          _ = MonoidAlgebra.of (ZMod p) (FreeGroup α) ((FreeGroup.of j)⁻¹) *
              (1 - MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of j)) := by rw [key]
          _ = MonoidAlgebra.of (ZMod p) (FreeGroup α) ((FreeGroup.of j)⁻¹) - 1 := by
                rw [mul_sub, mul_one, hmm]
      exact h3
  | mul x y hx hy =>
      rw [F_mul, hx, hy, map_mul]
      noncomm_ring

set_option linter.unusedVariables false in
lemma fox_lin (z : W p α) :
    ∑ i : α, Dlin p α i z * t p α i
      = z - algebraMap (ZMod p) (W p α) (aug p α z) := by
  induction z using MonoidAlgebra.induction_on with
  | of g =>
      have h1 : F p α g = ∑ i : α, Dfun p α i g * t p α i := rfl
      simp only [Dlin_of, ← h1, fox_group p α g, aug_of, map_one]
  | add x y hx hy =>
      simp only [map_add, add_mul, Finset.sum_add_distrib, hx, hy, sub_add_sub_comm]
  | smul r x hx =>
      have h2 : ∑ i : α, Dlin p α i (r • x) * t p α i
          = r • ∑ i : α, Dlin p α i x * t p α i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, smul_mul_assoc]
      have haug : algebraMap (ZMod p) (W p α) (aug p α (r • x))
          = r • algebraMap (ZMod p) (W p α) (aug p α x) := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.smul_def, map_mul, Algebra.algebraMap_self_apply]
      rw [h2, hx, haug, smul_sub]

/-- Fox's formula linearised: `Ψ ∘ Ψinv = id` on the augmentation ideal. -/
lemma Psi_PsiInv (z : W p α) (hz : z ∈ IW p α) : Psi p α (PsiInv p α z) = z := by
  have h := fox_lin p α z
  rw [mem_IW_iff] at hz
  rw [Psi, show PsiInv p α z = fun i => Dlin p α i z from rfl, h, hz, map_zero, sub_zero]

end ScratchGS

-- ===== end of scratchFox_gs =====


noncomputable section
open MonoidAlgebra

namespace Commons.GroupTheory.ProPGroup

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]

abbrev FW := MonoidAlgebra (ZMod p) (FreeGroup α)

/-- The algebra map `F_p[FreeGroup α] →ₐ[F_p] F_p[G]` induced by `π`. -/
noncomputable def rho {G : Type*} [Group G] (π : FreeGroup α →* G) :
    FW p α →ₐ[ZMod p] MonoidAlgebra (ZMod p) G :=
  MonoidAlgebra.lift (ZMod p) (MonoidAlgebra (ZMod p) G) (FreeGroup α)
    ((MonoidAlgebra.of (ZMod p) G).comp π)

lemma rho_of {G : Type*} [Group G] (π : FreeGroup α →* G) (g : FreeGroup α) :
    rho p α π (MonoidAlgebra.of (ZMod p) (FreeGroup α) g) =
      MonoidAlgebra.of (ZMod p) G (π g) := by
  simp [rho]

/-- The kernel ideal of `ρ`. -/
def JrelK {G : Type*} [Group G] (π : FreeGroup α →* G) : Ideal (FW p α) :=
  RingHom.ker (rho p α π).toRingHom

lemma relator_mem_JrelK {G : Type*} [Group G] (π : FreeGroup α →* G) {g : FreeGroup α}
    (hg : π g = 1) : (MonoidAlgebra.of (ZMod p) (FreeGroup α) g - 1) ∈ JrelK p α π := by
  rw [JrelK, RingHom.mem_ker]
  change rho p α π (MonoidAlgebra.of (ZMod p) (FreeGroup α) g - 1) = 0
  rw [map_sub]
  change rho p α π (MonoidAlgebra.of (ZMod p) (FreeGroup α) g) - rho p α π 1 = 0
  rw [rho_of, hg, map_one (MonoidAlgebra.of (ZMod p) G), map_one (rho p α π), sub_self]

namespace ScratchSerre

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]

local notation "MO" => MonoidAlgebra.of (ZMod p) (FreeGroup α)

def hullRel (rel : Finset (FreeGroup α)) : Ideal (FW p α) :=
  ⊤ * Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α))) * ⊤

lemma hullRel_isTwoSided (rel : Finset (FreeGroup α)) : (hullRel p α rel).IsTwoSided := by
  refine Ideal.IsTwoSided.mk (fun b ha => ?_)
  have hle : hullRel p α rel * (⊤ : Ideal (FW p α)) ≤ hullRel p α rel := by
    rw [hullRel]
    rw [mul_assoc, Ideal.mul_top, Ideal.top_mul]
  exact hle (Submodule.mul_mem_mul ha Submodule.mem_top)

instance hullRel_isTwoSided_inst (rel : Finset (FreeGroup α)) : (hullRel p α rel).IsTwoSided :=
  hullRel_isTwoSided p α rel

lemma relator_mem_hullRel (rel : Finset (FreeGroup α)) {r : FreeGroup α}
    (hr : r ∈ (rel : Set (FreeGroup α))) : MO r - 1 ∈ hullRel p α rel := by
  rw [hullRel]
  have hI : MO r - 1 ∈ Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α))) :=
    Ideal.subset_span ⟨r, hr, rfl⟩
  have h1 : MO r - 1 ∈ (⊤ : Ideal (FW p α)) * Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α))) := by
    rw [Ideal.top_mul]
    exact hI
  have h2 : (⊤ : Ideal (FW p α)) * Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α))) ≤
      (⊤ : Ideal (FW p α)) * Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α))) * ⊤ := by
    intro x hx
    simpa using Submodule.mul_mem_mul hx (Submodule.mem_top : (1 : FW p α) ∈ (⊤ : Ideal (FW p α)))
  exact h2 h1

lemma relator_mul (g h : FreeGroup α) :
    MO (g * h) - 1 = (MO g - 1) + (MO g - 1) * (MO h - 1) + (MO h - 1) := by
  rw [map_mul]
  noncomm_ring

lemma relator_inv (g : FreeGroup α) :
    MO g⁻¹ - 1 = -MO g⁻¹ * (MO g - 1) := by
  have h : MO g⁻¹ * MO g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc MO g⁻¹ - 1 = MO g⁻¹ - MO g⁻¹ * MO g := by rw [h]
    _ = -MO g⁻¹ * (MO g - 1) := by noncomm_ring

lemma relator_conj (f r : FreeGroup α) :
    MO (f * r * f⁻¹) - 1 = MO f * (MO r - 1) * MO f⁻¹ := by
  rw [map_mul, map_mul]
  have h : MO f * MO f⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc MO f * MO r * MO f⁻¹ - 1 = MO f * MO r * MO f⁻¹ - MO f * MO f⁻¹ := by rw [h]
    _ = MO f * (MO r - 1) * MO f⁻¹ := by noncomm_ring

lemma relator_mem_hullRel_of_mem_normalClosure (rel : Finset (FreeGroup α)) {g : FreeGroup α}
    (hg : g ∈ Subgroup.normalClosure (rel : Set (FreeGroup α))) : MO g - 1 ∈ hullRel p α rel := by
  classical
  haveI : (hullRel p α rel).IsTwoSided := hullRel_isTwoSided p α rel
  -- normalClosure = closure (conjugatesOfSet rel)
  refine Subgroup.closure_induction (k := Group.conjugatesOfSet (rel : Set (FreeGroup α))) ?_ ?_ ?_ ?_ hg
  · intro x hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨r, hr, hconj⟩
    rcases isConj_iff.mp hconj with ⟨f, hf⟩
    rw [← hf, relator_conj]
    have hκ : MO r - 1 ∈ hullRel p α rel := relator_mem_hullRel p α rel hr
    have h1 : (MO r - 1) * MO f⁻¹ ∈ hullRel p α rel :=
      Ideal.mul_mem_right _ _ hκ
    simpa [mul_assoc] using Ideal.mul_mem_left _ (MO f) h1
  · simp [MonoidAlgebra.one_def]
  · intro x y hx hy hxP hyP
    rw [relator_mul]
    exact Ideal.add_mem _ (Ideal.add_mem _ hxP (Ideal.mul_mem_right _ _ hxP)) hyP
  · intro x hx hxP
    rw [relator_inv]
    exact Ideal.mul_mem_left _ _ hxP

end ScratchSerre

namespace ScratchSerre

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]
variable {G : Type*} [Group G] (π : FreeGroup α →* G) (hπ : Function.Surjective π)
  (rel : Finset (FreeGroup α)) (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)

local notation "MO" => MonoidAlgebra.of (ZMod p) (FreeGroup α)

/-- The group hom `Γ →* (W ⧸ I)ˣ` induced by the group algebra. -/
noncomputable def phiUnits : FreeGroup α →* (FW p α ⧸ hullRel p α rel)ˣ where
  toFun g := Units.mk (Ideal.Quotient.mk (hullRel p α rel) (MO g))
      (Ideal.Quotient.mk (hullRel p α rel) (MO g⁻¹))
      (by
        have hmul : MO g * MO g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        rw [show Ideal.Quotient.mk (hullRel p α rel) (MO g) * Ideal.Quotient.mk (hullRel p α rel) (MO g⁻¹)
            = Ideal.Quotient.mk (hullRel p α rel) (MO g * MO g⁻¹) from (map_mul _ _ _).symm,
          hmul, map_one])
      (by
        have hmul : MO g⁻¹ * MO g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        rw [show Ideal.Quotient.mk (hullRel p α rel) (MO g⁻¹) * Ideal.Quotient.mk (hullRel p α rel) (MO g)
            = Ideal.Quotient.mk (hullRel p α rel) (MO g⁻¹ * MO g) from (map_mul _ _ _).symm,
          hmul, map_one])
  map_one' := by
    ext
    change Ideal.Quotient.mk (hullRel p α rel) (MonoidAlgebra.of (ZMod p) (FreeGroup α) 1) = 1
    rw [map_one, map_one]
  map_mul' g h := by
    ext
    change Ideal.Quotient.mk (hullRel p α rel) (MO (g * h)) =
      Ideal.Quotient.mk (hullRel p α rel) (MO g) * Ideal.Quotient.mk (hullRel p α rel) (MO h)
    rw [map_mul, map_mul]

lemma phiUnits_ker_rel : (rel : Set (FreeGroup α)) ⊆ (phiUnits p α rel).ker := by
  intro r hr
  change phiUnits p α rel r = 1
  ext
  change Ideal.Quotient.mk (hullRel p α rel) (MO r) = Ideal.Quotient.mk (hullRel p α rel) 1
  rw [Ideal.Quotient.eq]
  simpa [MonoidAlgebra.one_def, sub_eq_add_neg] using relator_mem_hullRel p α rel hr

lemma phiUnits_ker (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    π.ker ≤ (phiUnits p α rel).ker := by
  rw [← hrel]
  exact Subgroup.normalClosure_le_normal (phiUnits_ker_rel p α rel)

/-- Well-definedness: if `π a = π b`, then `phiUnits a = phiUnits b`. -/
lemma phiUnits_eq_of_apply_eq (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    {a b : FreeGroup α} (h : π a = π b) : phiUnits p α rel a = phiUnits p α rel b := by
  have hab : a * b⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hker : a * b⁻¹ ∈ (phiUnits p α rel).ker := phiUnits_ker p α π rel hrel hab
  rw [MonoidHom.mem_ker] at hker
  have hmul : phiUnits p α rel a * (phiUnits p α rel b)⁻¹ = 1 := by
    simpa [map_mul, map_inv] using hker
  exact mul_inv_eq_one.mp hmul

/-- The induced group hom `G →* (W ⧸ I)ˣ`, defined by choosing preimages. -/
noncomputable def psiUnits (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    G →* (FW p α ⧸ hullRel p α rel)ˣ where
  toFun g := phiUnits p α rel (Classical.choose (hπ g))
  map_one' := by
    apply phiUnits_eq_of_apply_eq p α π rel hrel
    rw [Classical.choose_spec (hπ 1), map_one]
  map_mul' g h := by
    have hv : π (Classical.choose (hπ (g * h))) =
        π (Classical.choose (hπ g) * Classical.choose (hπ h)) := by
      rw [map_mul, Classical.choose_spec (hπ g), Classical.choose_spec (hπ h),
        Classical.choose_spec (hπ (g * h))]
    calc phiUnits p α rel (Classical.choose (hπ (g * h)))
        = phiUnits p α rel (Classical.choose (hπ g) * Classical.choose (hπ h)) :=
          phiUnits_eq_of_apply_eq p α π rel hrel hv
      _ = phiUnits p α rel (Classical.choose (hπ g)) * phiUnits p α rel (Classical.choose (hπ h)) := by
          rw [map_mul]

/-- The algebra map `F_p[G] →ₐ[F_p] W ⧸ I`. -/
noncomputable def psibar :
    MonoidAlgebra (ZMod p) G →ₐ[ZMod p] (FW p α ⧸ hullRel p α rel) :=
  MonoidAlgebra.lift (ZMod p) (FW p α ⧸ hullRel p α rel) G
    ((Units.coeHom (FW p α ⧸ hullRel p α rel)).comp (psiUnits p α π hπ rel hrel))

lemma psibar_of (g : G) :
    psibar p α π hπ rel hrel (MonoidAlgebra.of (ZMod p) G g) =
      (psiUnits p α π hπ rel hrel g : FW p α ⧸ hullRel p α rel) := by
  simp [psibar]

lemma psibar_rho (g : FreeGroup α) :
    psibar p α π hπ rel hrel (rho p α π (MO g)) =
      Ideal.Quotient.mk (hullRel p α rel) (MO g) := by
  rw [rho_of, psibar_of]
  change (phiUnits p α rel (Classical.choose (hπ (π g))) : FW p α ⧸ hullRel p α rel) =
    Ideal.Quotient.mk (hullRel p α rel) (MO g)
  have hchoose : π (Classical.choose (hπ (π g))) = π g := Classical.choose_spec (hπ (π g))
  have heq := phiUnits_eq_of_apply_eq p α π rel hrel hchoose
  rw [heq]
  rfl

end ScratchSerre

namespace ScratchSerre

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]
variable {G : Type*} [Group G] (π : FreeGroup α →* G) (hπ : Function.Surjective π)
  (rel : Finset (FreeGroup α)) (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)

local notation "MO" => MonoidAlgebra.of (ZMod p) (FreeGroup α)

lemma psibar_rho_eq (z : FW p α) :
    psibar p α π hπ rel hrel (rho p α π z) =
      Ideal.Quotient.mk (hullRel p α rel) z := by
  induction z using MonoidAlgebra.induction_on with
  | of g => exact psibar_rho p α π hπ rel hrel g
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | smul r x hx =>
      rw [map_smul (rho p α π) r x, map_smul (psibar p α π hπ rel hrel) r ((rho p α π) x), hx]
      rfl

instance JrelK_isTwoSided : (JrelK p α π).IsTwoSided := by
  refine Ideal.IsTwoSided.mk ?_
  intro a b ha
  change rho p α π (a * b) = 0
  rw [map_mul, show rho p α π a = 0 from ha, zero_mul]

lemma hullRel_le_JrelK (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    hullRel p α rel ≤ JrelK p α π := by
  rw [hullRel]
  have hspan : Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α))) ≤
      JrelK p α π := by
    rw [Ideal.span_le]
    rintro x ⟨r, hr, rfl⟩
    have hrker : r ∈ π.ker := by
      rw [← hrel]
      exact Subgroup.subset_normalClosure hr
    exact relator_mem_JrelK p α π (MonoidHom.mem_ker.mp hrker)
  calc ⊤ * Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α))) * ⊤
      ≤ ⊤ * JrelK p α π * ⊤ := Ideal.mul_mono (Ideal.mul_mono le_top hspan) le_top
    _ = JrelK p α π := by rw [Ideal.top_mul, Ideal.mul_top]

lemma JrelK_le_hullRel (hπ : Function.Surjective π)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    JrelK p α π ≤ hullRel p α rel := by
  intro z hz
  have hz' : rho p α π z = 0 := by
    simpa [JrelK] using hz
  have h := psibar_rho_eq p α π hπ rel hrel z
  rw [hz', map_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.mp h.symm

theorem JrelK_eq_hullRel (hπ : Function.Surjective π)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    JrelK p α π = hullRel p α rel :=
  le_antisymm
    (JrelK_le_hullRel (p := p) (α := α) (π := π) (hπ := hπ) (rel := rel) (hrel := hrel))
    (hullRel_le_JrelK (p := p) (α := α) (π := π) (rel := rel) (hrel := hrel))

end ScratchSerre

namespace ScratchSerre

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]

local notation "MO" => MonoidAlgebra.of (ZMod p) (FreeGroup α)
local notation "K" => ZMod p

abbrev relSpan (rel : Finset (FreeGroup α)) : Ideal (FW p α) :=
  Ideal.span ((fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α)))

lemma aug_algebraMap (c : K) :
    ScratchGS.aug p α (algebraMap K (FW p α) c) = c := by
  simpa using (ScratchGS.aug p α).commutes c

lemma mul_relator_mul_algebraMap (r : FreeGroup α) (f : FW p α) (c : K) :
    f * (MO r - 1) * algebraMap K (FW p α) c =
      algebraMap K (FW p α) c * (f * (MO r - 1)) := by
  calc f * (MO r - 1) * algebraMap K (FW p α) c
      = f * ((MO r - 1) * algebraMap K (FW p α) c) := by rw [mul_assoc]
    _ = f * (algebraMap K (FW p α) c * (MO r - 1)) := by
          rw [← Algebra.commutes c (MO r - 1)]
    _ = (f * algebraMap K (FW p α) c) * (MO r - 1) := by rw [← mul_assoc]
    _ = (algebraMap K (FW p α) c * f) * (MO r - 1) := by
          rw [← Algebra.commutes c f]
    _ = algebraMap K (FW p α) c * (f * (MO r - 1)) := by rw [mul_assoc]

lemma relator_mul_decomp (r : FreeGroup α) (f1 f2 : FW p α) :
    f1 * (MO r - 1) * f2 =
      algebraMap K (FW p α) (ScratchGS.aug p α f2) * (f1 * (MO r - 1)) +
        f1 * (MO r - 1) * (f2 - algebraMap K (FW p α) (ScratchGS.aug p α f2)) := by
  have h : f2 = algebraMap K (FW p α) (ScratchGS.aug p α f2) +
      (f2 - algebraMap K (FW p α) (ScratchGS.aug p α f2)) := by abel
  conv_lhs => rw [h]
  rw [mul_add]
  congr 1
  exact mul_relator_mul_algebraMap p α r f1 (ScratchGS.aug p α f2)

lemma relator_mul_mem_span_add
    (rel : Finset (FreeGroup α)) {G : Type*} [Group G] (π : FreeGroup α →* G)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    {r : FreeGroup α} (hr : r ∈ (rel : Set (FreeGroup α))) (f1 f2 : FW p α) :
    f1 * (MO r - 1) * f2 ∈ relSpan p α rel + JrelK p α π * ScratchGS.IW p α := by
  let c : FW p α := algebraMap K (FW p α) (ScratchGS.aug p α f2)
  have hdecomp := relator_mul_decomp p α r f1 f2
  rw [hdecomp]
  refine Submodule.add_mem _ ?_ ?_
  · have hmem : MO r - 1 ∈ (fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α)) :=
      Set.mem_image_of_mem (fun r : FreeGroup α => MO r - 1) hr
    exact Ideal.mul_mem_left _ c (Ideal.mul_mem_left _ f1 (Submodule.mem_sup_left (Ideal.subset_span hmem)))
  · have hrker : r ∈ π.ker := by
      rw [← hrel]
      exact Subgroup.subset_normalClosure hr
    have hκJ : f1 * (MO r - 1) ∈ JrelK p α π :=
      Ideal.mul_mem_left _ f1 (relator_mem_JrelK p α π (MonoidHom.mem_ker.mp hrker))
    have hdiff : f2 - c ∈ ScratchGS.IW p α := by
      rw [ScratchGS.mem_IW_iff]
      change ScratchGS.aug p α (f2 - c) = 0
      rw [map_sub, aug_algebraMap]
      abel
    exact Submodule.mem_sup_right (Ideal.mul_mem_mul hκJ hdiff)

lemma relSpan_mul_mem
    (rel : Finset (FreeGroup α)) {G : Type*} [Group G] (π : FreeGroup α →* G)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    ∀ (s : FW p α), s ∈ relSpan p α rel → ∀ (f1 f2 : FW p α),
      f1 * s * f2 ∈ relSpan p α rel + JrelK p α π * ScratchGS.IW p α := by
  intro s hs
  refine Submodule.span_induction (R := FW p α) (M := FW p α)
    (s := (fun r : FreeGroup α => MO r - 1) '' (rel : Set (FreeGroup α)))
    (p := fun s _ => ∀ (f1 f2 : FW p α),
      f1 * s * f2 ∈ relSpan p α rel + JrelK p α π * ScratchGS.IW p α)
    ?_ ?_ ?_ ?_ hs
  · intro x hx f1 f2
    rcases hx with ⟨r, hr, rfl⟩
    exact relator_mul_mem_span_add p α rel π hrel hr f1 f2
  · intro f1 f2
    simp
  · intro x y hx hy hxP hyP f1 f2
    rw [mul_add, add_mul]
    exact Submodule.add_mem _ (hxP f1 f2) (hyP f1 f2)
  · intro c x hx hxP f1 f2
    -- `c • x = c * x`; use the induction hypothesis with `f1 * c`.
    change f1 * (c * x) * f2 ∈ relSpan p α rel + JrelK p α π * ScratchGS.IW p α
    simpa [mul_assoc] using hxP (f1 * c) f2

lemma hullRel_le_relSpan_add_JmulIW
    (rel : Finset (FreeGroup α)) {G : Type*} [Group G] (π : FreeGroup α →* G)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    hullRel p α rel ≤ relSpan p α rel + JrelK p α π * ScratchGS.IW p α := by
  rw [hullRel]
  rw [Ideal.mul_le]
  intro a ha b hb
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro u hu s hs
    exact relSpan_mul_mem p α rel π hrel s hs u b
  · intro x y hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy

theorem JrelK_eq_relSpan_add_JmulIW
    (rel : Finset (FreeGroup α)) {G : Type*} [Group G] (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    JrelK p α π = relSpan p α rel + JrelK p α π * ScratchGS.IW p α := by
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [JrelK_eq_hullRel p α π rel hπ hrel]
    exact hullRel_le_relSpan_add_JmulIW p α rel π hrel
  · have hspan : relSpan p α rel ≤ JrelK p α π := by
      rw [relSpan, Ideal.span_le]
      rintro x ⟨r, hr, rfl⟩
      have hrker : r ∈ π.ker := by
        rw [← hrel]
        exact Subgroup.subset_normalClosure hr
      exact relator_mem_JrelK p α π (MonoidHom.mem_ker.mp hrker)
    have hmul : JrelK p α π * ScratchGS.IW p α ≤ JrelK p α π := by
      rw [Ideal.mul_le]
      intro j hj iw hiw
      exact Ideal.mul_mem_right iw _ hj
    exact sup_le hspan hmul

end ScratchSerre

-- ===== end of scratch_serre_core =====


noncomputable section
open MonoidAlgebra

namespace ScratchSerre

def augB (p : ℕ) (G : Type*) [Group G] :
    MonoidAlgebra (ZMod p) G →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) G (1 : G →* ZMod p)

abbrev bG (p : ℕ) (G : Type*) [Group G] : Ideal (MonoidAlgebra (ZMod p) G) :=
  RingHom.ker (augB p G).toRingHom

def tG (p : ℕ) (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α]
    (π : FreeGroup α →* G) (i : α) : MonoidAlgebra (ZMod p) G :=
  MonoidAlgebra.of (ZMod p) G (π (FreeGroup.of i)) - 1

lemma augB_of (p : ℕ) (G : Type*) [Group G] (g : G) :
    augB p G (MonoidAlgebra.of (ZMod p) G g) = 1 := by
  simp [augB]

lemma tG_mem_bG (p : ℕ) (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α]
    (π : FreeGroup α →* G) (i : α) : tG p G α π i ∈ bG p G := by
  rw [bG, RingHom.mem_ker]
  change augB p G (MonoidAlgebra.of (ZMod p) G (π (FreeGroup.of i)) - 1) = 0
  rw [map_sub, augB_of]
  simp

def Phi (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α]
    (π : FreeGroup α →* G) : (α → MonoidAlgebra (ZMod p) G) →ₗ[ZMod p] bG p G where
  toFun q := ⟨∑ i, q i * tG p G α π i, by
    rw [bG, RingHom.mem_ker]
    change augB p G (∑ i, q i * tG p G α π i) = 0
    rw [map_sum]
    refine Finset.sum_eq_zero ?_
    intro i _
    have hmem := tG_mem_bG p G α π i
    rw [bG, RingHom.mem_ker] at hmem
    change augB p G (tG p G α π i) = 0 at hmem
    rw [map_mul, hmem, mul_zero]
  ⟩
  map_add' := by
    intro q r
    apply Subtype.ext
    simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c q
    apply Subtype.ext
    change (∑ x, (c • q x) * tG p G α π x) = c • (∑ i, q i * tG p G α π i)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Algebra.smul_mul_assoc]

end ScratchSerre

-- ===== end of scratch_serre_basic =====


noncomputable section
open MonoidAlgebra

namespace ScratchSerre

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]
variable (G : Type*) [Group G]

local notation "K" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) G
local notation "W" => MonoidAlgebra (ZMod p) (FreeGroup α)

/-- The relator element `κ_r = MO r - 1` in the free group algebra. -/
def kappa (r : FreeGroup α) : W := MonoidAlgebra.of (ZMod p) (FreeGroup α) r - 1

lemma kappa_mem_IW (r : FreeGroup α) : kappa p α r ∈ ScratchGS.IW p α := by
  rw [ScratchGS.mem_IW_iff]
  change ScratchGS.aug p α (MonoidAlgebra.of (ZMod p) (FreeGroup α) r - 1) = 0
  rw [map_sub, ScratchGS.aug_of, map_one, sub_self]

lemma rho_t (π : FreeGroup α →* G) (i : α) :
    Commons.GroupTheory.ProPGroup.rho p α π (ScratchGS.t p α i) = tG p G α π i := by
  change Commons.GroupTheory.ProPGroup.rho p α π
      (MonoidAlgebra.of (ZMod p) (FreeGroup α) (FreeGroup.of i) - 1) =
    MonoidAlgebra.of (ZMod p) G (π (FreeGroup.of i)) - 1
  rw [map_sub, Commons.GroupTheory.ProPGroup.rho_of, map_one]

lemma rho_kappa_eq_zero (rel : Finset (FreeGroup α)) (π : FreeGroup α →* G)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    {r : FreeGroup α} (hr : r ∈ (rel : Set (FreeGroup α))) :
    Commons.GroupTheory.ProPGroup.rho p α π (kappa p α r) = 0 := by
  have hrker : r ∈ π.ker := by
    rw [← hrel]
    exact Subgroup.subset_normalClosure hr
  exact Commons.GroupTheory.ProPGroup.relator_mem_JrelK p α π (MonoidHom.mem_ker.mp hrker)

/-- The Koszul differential on the relator module. -/
def dRel (rel : Finset (FreeGroup α)) (π : FreeGroup α →* G) :
    (rel → B) →ₗ[K] (α → B) where
  toFun f i := ∑ r : rel, f r * Commons.GroupTheory.ProPGroup.rho p α π
    (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)))
  map_add' := by
    intro f g
    funext i
    change (∑ r : rel, (f r + g r) *
        Commons.GroupTheory.ProPGroup.rho p α π
          (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)))) =
      (∑ r : rel, f r * Commons.GroupTheory.ProPGroup.rho p α π
          (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)))) +
        (∑ r : rel, g r * Commons.GroupTheory.ProPGroup.rho p α π
          (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α))))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [add_mul]
  map_smul' := by
    intro c f
    funext i
    change (∑ r : rel, (c • f r) *
        Commons.GroupTheory.ProPGroup.rho p α π
          (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)))) =
      c • (∑ r : rel, f r * Commons.GroupTheory.ProPGroup.rho p α π
          (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α))))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Algebra.smul_mul_assoc]

lemma dRel_eval (rel : Finset (FreeGroup α)) (π : FreeGroup α →* G)
    (f : rel → B) :
    (∑ i : α, dRel p α G rel π f i * tG p G α π i) =
      ∑ r : rel, f r * Commons.GroupTheory.ProPGroup.rho p α π (kappa p α (r : FreeGroup α)) := by
  change (∑ i : α, (∑ r : rel, f r * Commons.GroupTheory.ProPGroup.rho p α π
      (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)))) * tG p G α π i) =
    ∑ r : rel, f r * Commons.GroupTheory.ProPGroup.rho p α π (kappa p α (r : FreeGroup α))
  simp_rw [Finset.sum_mul (Finset.univ : Finset rel)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro r _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum (Finset.univ : Finset α)]
  congr 1
  have hfox := ScratchGS.Psi_PsiInv p α (kappa p α (r : FreeGroup α))
    (kappa_mem_IW p α (r : FreeGroup α))
  calc (∑ i : α, Commons.GroupTheory.ProPGroup.rho p α π
          (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α))) * tG p G α π i)
      = ∑ i : α, Commons.GroupTheory.ProPGroup.rho p α π
          (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)) * ScratchGS.t p α i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [map_mul, rho_t]
    _ = Commons.GroupTheory.ProPGroup.rho p α π
          (∑ i : α, ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)) * ScratchGS.t p α i) := by
        rw [map_sum]
    _ = Commons.GroupTheory.ProPGroup.rho p α π (kappa p α (r : FreeGroup α)) := by
        rw [show (∑ i : α, ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)) *
            ScratchGS.t p α i) = kappa p α (r : FreeGroup α) from by
          simpa [ScratchGS.Psi, ScratchGS.PsiInv] using hfox]

lemma Phi_dRel_eq_zero (rel : Finset (FreeGroup α)) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    (f : rel → B) :
    Phi p G α π (dRel p α G rel π f) = 0 := by
  apply Subtype.ext
  change (∑ i : α, dRel p α G rel π f i * tG p G α π i) = 0
  rw [dRel_eval]
  refine Finset.sum_eq_zero ?_
  intro r _
  rw [rho_kappa_eq_zero p α G rel π hrel r.2, mul_zero]

end ScratchSerre

-- ===== end of scratch_serre_partial =====


noncomputable section
open MonoidAlgebra

namespace ScratchSerre

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]
variable (G : Type*) [Group G]

local notation "K" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) G
local notation "W" => MonoidAlgebra (ZMod p) (FreeGroup α)


lemma rho_surjective (π : FreeGroup α →* G) (hπ : Function.Surjective π) :
    Function.Surjective (Commons.GroupTheory.ProPGroup.rho p α π) := by
  intro z
  induction z using MonoidAlgebra.induction_on with
  | of g =>
      obtain ⟨x, rfl⟩ := hπ g
      exact ⟨MonoidAlgebra.of (ZMod p) (FreeGroup α) x,
        by rw [Commons.GroupTheory.ProPGroup.rho_of]⟩
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [map_add]⟩
  | smul c x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨c • a, by rw [map_smul]⟩

lemma Psi_mul (a : W) (q : α → W) :
    ScratchGS.Psi p α (a • q) = a * ScratchGS.Psi p α q := by
  simp [ScratchGS.Psi, Finset.mul_sum, mul_assoc]

lemma PsiInv_mul (a : W) {z : W} (hz : z ∈ ScratchGS.IW p α) :
    ScratchGS.PsiInv p α (a * z) = a • ScratchGS.PsiInv p α z := by
  have h2 : ScratchGS.Psi p α (a • ScratchGS.PsiInv p α z) = a * z := by
    rw [Psi_mul, ScratchGS.Psi_PsiInv p α z hz]
  have h := congrArg (ScratchGS.PsiInv p α) h2
  simpa [ScratchGS.PsiInv_Psi] using h.symm


lemma Psi_injective : Function.Injective (ScratchGS.Psi p α) := by
  intro a b h
  have h' := congrArg (ScratchGS.PsiInv p α) h
  simpa [ScratchGS.PsiInv_Psi] using h'

lemma PsiInv_relSpan (rel : Finset (FreeGroup α)) {s0 : W}
    (hs0 : s0 ∈ Commons.GroupTheory.ProPGroup.ScratchSerre.relSpan p α rel) :
    ∃ f : rel → W, ScratchGS.PsiInv p α s0 =
      ∑ r : rel, f r • ScratchGS.PsiInv p α (kappa p α (r : FreeGroup α)) := by
  let P : W → Prop := fun s => ∃ f : rel → W,
    ScratchGS.PsiInv p α s = ∑ r : rel, f r • ScratchGS.PsiInv p α (kappa p α (r : FreeGroup α))
  have hspan : ∀ s ∈ Commons.GroupTheory.ProPGroup.ScratchSerre.relSpan p α rel, P s := by
    intro s hs
    refine Submodule.span_induction (R := W) (M := W)
      (s := (fun r : FreeGroup α => MonoidAlgebra.of (ZMod p) (FreeGroup α) r - 1) ''
        (rel : Set (FreeGroup α))) (p := fun s _ => P s) ?_ ?_ ?_ ?_ hs
    · intro x hx
      rcases hx with ⟨r, hr, rfl⟩
      refine ⟨fun r' => if r' = ⟨r, hr⟩ then 1 else 0, ?_⟩
      change ScratchGS.PsiInv p α (kappa p α r) = _
      rw [Finset.sum_eq_single (⟨r, hr⟩ : rel)]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h; simp at h
    · refine ⟨0, ?_⟩
      ext i
      simp [ScratchGS.PsiInv]
    · intro x y hx hy hxP hyP
      rcases hxP with ⟨f, hf⟩
      rcases hyP with ⟨g, hg⟩
      refine ⟨f + g, ?_⟩
      have hsum : ScratchGS.PsiInv p α (x + y) =
          ScratchGS.PsiInv p α x + ScratchGS.PsiInv p α y := by
        ext i
        simp [ScratchGS.PsiInv]
      funext i
      rw [hsum, Pi.add_apply, congrFun hf i, congrFun hg i]
      rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [Pi.add_apply, add_smul, Pi.add_apply]
    · intro c x hx hxP
      rcases hxP with ⟨f, hf⟩
      have hxI : x ∈ ScratchGS.IW p α := by
        have hle : Commons.GroupTheory.ProPGroup.ScratchSerre.relSpan p α rel ≤ ScratchGS.IW p α := by
          rw [Commons.GroupTheory.ProPGroup.ScratchSerre.relSpan, Ideal.span_le]
          rintro x ⟨r, hr, rfl⟩
          exact kappa_mem_IW p α r
        exact hle hx
      refine ⟨fun r => c * f r, ?_⟩
      rw [show c • x = c * x by rfl, PsiInv_mul p α c hxI, hf, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [smul_smul]
  exact hspan s0 hs0


def rhoVec (π : FreeGroup α →* G) (v : α → W) : α → B :=
  fun i => Commons.GroupTheory.ProPGroup.rho p α π (v i)

lemma rho_PsiInv_relSpan (rel : Finset (FreeGroup α)) (π : FreeGroup α →* G)
    {s : W} (hs : s ∈ Commons.GroupTheory.ProPGroup.ScratchSerre.relSpan p α rel) :
    rhoVec p α G π (ScratchGS.PsiInv p α s) ∈
      LinearMap.range (dRel p α G rel π) := by
  rcases PsiInv_relSpan p α rel hs with ⟨f, hf⟩
  refine ⟨fun r => Commons.GroupTheory.ProPGroup.rho p α π (f r), ?_⟩
  funext i
  rw [hf]
  symm
  change Commons.GroupTheory.ProPGroup.rho p α π
      ((∑ r : rel, f r • ScratchGS.PsiInv p α (kappa p α (r : FreeGroup α))) i) =
    dRel p α G rel π (fun r => Commons.GroupTheory.ProPGroup.rho p α π (f r)) i
  rw [Finset.sum_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change Commons.GroupTheory.ProPGroup.rho p α π
      (f r * ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α))) =
    (fun r => Commons.GroupTheory.ProPGroup.rho p α π (f r)) r *
      Commons.GroupTheory.ProPGroup.rho p α π
        (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)))
  rw [map_mul]

lemma rhoVec_PsiInv_JmulIW_eq_zero (π : FreeGroup α →* G) {j : W}
    (hj : j ∈ Commons.GroupTheory.ProPGroup.JrelK p α π * ScratchGS.IW p α) :
    rhoVec p α G π (ScratchGS.PsiInv p α j) = 0 := by
  let P : W → Prop := fun j => rhoVec p α G π (ScratchGS.PsiInv p α j) = 0
  have hmain : ∀ j ∈ Commons.GroupTheory.ProPGroup.JrelK p α π * ScratchGS.IW p α, P j := by
    intro j hj
    refine Submodule.mul_induction_on hj ?_ ?_
    · intro k hk iw hiw
      funext i
      change Commons.GroupTheory.ProPGroup.rho p α π (ScratchGS.PsiInv p α (k * iw) i) = 0
      rw [PsiInv_mul p α k hiw]
      change Commons.GroupTheory.ProPGroup.rho p α π (k • ScratchGS.PsiInv p α iw i) = 0
      rw [show k • ScratchGS.PsiInv p α iw i = k * ScratchGS.PsiInv p α iw i by rfl,
        map_mul, show Commons.GroupTheory.ProPGroup.rho p α π k = 0 from hk, zero_mul]
    · intro x y hxP hyP
      funext i
      change Commons.GroupTheory.ProPGroup.rho p α π (ScratchGS.PsiInv p α (x + y) i) = 0
      have hsum : ScratchGS.PsiInv p α (x + y) =
          ScratchGS.PsiInv p α x + ScratchGS.PsiInv p α y := by
        ext i; simp [ScratchGS.PsiInv]
      rw [hsum]
      change Commons.GroupTheory.ProPGroup.rho p α π
        (ScratchGS.PsiInv p α x i + ScratchGS.PsiInv p α y i) = 0
      rw [map_add]
      change Commons.GroupTheory.ProPGroup.rho p α π (ScratchGS.PsiInv p α x i) +
          Commons.GroupTheory.ProPGroup.rho p α π (ScratchGS.PsiInv p α y i) = 0
      rw [show Commons.GroupTheory.ProPGroup.rho p α π (ScratchGS.PsiInv p α x i) = 0 from
            congrFun hxP i,
          show Commons.GroupTheory.ProPGroup.rho p α π (ScratchGS.PsiInv p α y i) = 0 from
            congrFun hyP i,
          add_zero]
  exact hmain j hj

lemma t_mem_IW (i : α) : ScratchGS.t p α i ∈ ScratchGS.IW p α := by
  rw [ScratchGS.mem_IW_iff]
  exact ScratchGS.aug_t p α i

lemma PsiInv_add (x y : W) :
    ScratchGS.PsiInv p α (x + y) = ScratchGS.PsiInv p α x + ScratchGS.PsiInv p α y := by
  ext i
  simp [ScratchGS.PsiInv]

lemma rhoVec_add (π : FreeGroup α →* G) (x y : α → W) :
    rhoVec p α G π (x + y) = rhoVec p α G π x + rhoVec p α G π y := by
  funext i
  simp [rhoVec, Pi.add_apply, map_add]

lemma ker_Phi_le_range_dRel (rel : Finset (FreeGroup α)) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    LinearMap.ker (Phi p G α π) ≤ LinearMap.range (dRel p α G rel π) := by
  intro q hq
  -- lift q to w
  choose w hw using fun i => rho_surjective p α G π hπ (q i)
  let z : W := ∑ i : α, w i * ScratchGS.t p α i
  have hz_rho : Commons.GroupTheory.ProPGroup.rho p α π z = 0 := by
    change Commons.GroupTheory.ProPGroup.rho p α π
      (∑ i : α, w i * ScratchGS.t p α i) = 0
    rw [map_sum]
    have hq0 : (∑ i : α, q i * tG p G α π i) = 0 := congrArg Subtype.val hq
    trans (∑ i : α, q i * tG p G α π i)
    · apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, hw i, rho_t]
    · exact hq0
  have hzJ : z ∈ Commons.GroupTheory.ProPGroup.JrelK p α π := by
    change Commons.GroupTheory.ProPGroup.rho p α π z = 0
    exact hz_rho
  have hz_mem : z ∈ Commons.GroupTheory.ProPGroup.ScratchSerre.relSpan p α rel +
      Commons.GroupTheory.ProPGroup.JrelK p α π * ScratchGS.IW p α := by
    rw [← Commons.GroupTheory.ProPGroup.ScratchSerre.JrelK_eq_relSpan_add_JmulIW p α rel π hπ hrel]
    exact hzJ
  rcases Submodule.mem_sup.mp hz_mem with ⟨s, hs, j, hj, hsj⟩
  have hz_eq : z = s + j := hsj.symm
  -- z ∈ IW
  have hzIW : z ∈ ScratchGS.IW p α := by
    change (∑ i : α, w i * ScratchGS.t p α i) ∈ ScratchGS.IW p α
    exact Submodule.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (t_mem_IW p α i))
  -- PsiInv z = w
  have hPsi_w : ScratchGS.Psi p α w = z := rfl
  have hPsi_PsiInv_z : ScratchGS.Psi p α (ScratchGS.PsiInv p α z) = z :=
    ScratchGS.Psi_PsiInv p α z hzIW
  have hw_eq : ScratchGS.PsiInv p α z = w := by
    apply Psi_injective p α
    rw [hPsi_PsiInv_z, hPsi_w]
  have hw_decomp : w = ScratchGS.PsiInv p α s + ScratchGS.PsiInv p α j := by
    rw [← hw_eq, hz_eq, PsiInv_add]
  have hw_q : rhoVec p α G π w = q := by
    funext i
    exact hw i
  have hq_eq : q = rhoVec p α G π (ScratchGS.PsiInv p α s) := by
    rw [← hw_q, hw_decomp, rhoVec_add]
    rw [rhoVec_PsiInv_JmulIW_eq_zero p α G π hj, add_zero]
  rcases rho_PsiInv_relSpan p α G rel π hs with ⟨f, hf⟩
  exact ⟨f, hf.trans hq_eq.symm⟩

end ScratchSerre

-- ===== end of scratch_serre_exact2 =====


noncomputable section


namespace ScratchSerre

open Module

variable {K B : Type*} [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]

/-- **General exact-sequence dimension lemma** over a field: if `0 → A → B → C → 0` is exact
then `dim B ≤ dim A + dim C`. -/
lemma finrank_le_add_of_exact {A C : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h : LinearMap.range f = LinearMap.ker g) :
    finrank K B ≤ finrank K A + finrank K C := by
  have h1 : finrank K (B ⧸ LinearMap.range f) + finrank K ↥(LinearMap.range f) = finrank K B :=
    Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have h2 : finrank K ↥(LinearMap.range f) ≤ finrank K A := by
    have := LinearMap.finrank_range_add_finrank_ker f
    omega
  have h3 : finrank K (B ⧸ LinearMap.range f) ≤ finrank K C := by
    rw [h, LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange g)]
    have h4 : finrank K ↥(LinearMap.range g) ≤ finrank K ↥(⊤ : Submodule K C) :=
      Submodule.finrank_mono le_top
    simpa using h4
  omega

/-- **Step 1 of the Serre recurrence.** The image of the augmentation ideal `b` in `B ⧸ b^(n+1)`
has dimension `dim (B ⧸ b^(n+1)) - 1`, provided `dim (B ⧸ b) = 1`. -/
lemma finrank_image_mkQ_pow_eq_sub_one
    (b : Ideal B) (n : ℕ) (hquot : finrank K (B ⧸ b) = 1) :
    finrank K ↥((Submodule.map (Submodule.mkQ (b ^ (n + 1))) (b : Submodule B B)).restrictScalars K) =
      finrank K (B ⧸ b ^ (n + 1)) - 1 := by
  have hle : (b ^ (n + 1) : Ideal B) ≤ b := Ideal.pow_le_self (by omega)
  let g : (B ⧸ b ^ (n + 1)) →ₗ[K] (B ⧸ b) :=
    (Submodule.mapQ (b ^ (n + 1)) (b : Submodule B B) (LinearMap.id : B →ₗ[B] B)
      (by simpa using hle)).restrictScalars K
  have hrange : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    refine Submodule.Quotient.induction_on (b : Submodule B B) x (fun y => ?_)
    exact ⟨Submodule.Quotient.mk y, by
      rw [LinearMap.restrictScalars_apply, Submodule.mapQ_apply]
      rfl⟩
  have hker : LinearMap.ker g =
      (Submodule.map (Submodule.mkQ (b ^ (n + 1))) (b : Submodule B B)).restrictScalars K := by
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (b ^ (n + 1)) x
      rw [LinearMap.restrictScalars_apply, Submodule.mapQ_apply] at hx
      have hy : y ∈ b := (Submodule.Quotient.mk_eq_zero b).mp hx
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
        Submodule.mapQ_apply]
      exact (Submodule.Quotient.mk_eq_zero b).mpr hy
  have hgr := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker] at hgr
  rw [finrank_top] at hgr
  rw [hquot] at hgr
  have hge : 1 ≤ finrank K (B ⧸ b ^ (n + 1)) := by omega
  have hgoal : finrank K (B ⧸ b ^ (n + 1)) =
      finrank K ↥((Submodule.map (Submodule.mkQ (b ^ (n + 1))) (b : Submodule B B)).restrictScalars K) + 1 := by
    rw [← hgr, Nat.add_comm]
  exact ((Nat.sub_eq_iff_eq_add hge).mpr hgoal).symm

end ScratchSerre

end

end

-- ===== end of scratch_serre_dim =====


open Module

namespace GSGen

open Finset

/-- `σ_n = b_0 + ... + b_n`. -/
def gsig (b : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n+1), b j

lemma gsig_succ (b : ℕ → ℕ) (n : ℕ) : gsig b (n+1) = gsig b n + b (n+1) := by
  simp only [gsig, Finset.sum_range_succ]

lemma gsig_zero (b : ℕ → ℕ) : gsig b 0 = b 0 := by
  simp [gsig]

/-- **Geometric identity**: `(1-x)·Σ_{k≤n} σ_k x^k = Σ_{j≤n} b_j x^j - σ_n x^{n+1}`. -/
lemma geom_gsig (b : ℕ → ℕ) (x : ℝ) (n : ℕ) :
    (1 - x) * (∑ k ∈ Finset.range (n+1), (gsig b k : ℝ) * x^k) =
      (∑ j ∈ Finset.range (n+1), (b j : ℝ) * x^j) - (gsig b n : ℝ) * x^(n+1) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one, Finset.sum_range_one, gsig_zero]
      ring
  | succ n ih =>
      conv_lhs => rw [Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [mul_add, ih, gsig_succ]
      push_cast
      ring

lemma geom_shift (x : ℝ) (n : ℕ) : (1 - x) * (∑ k ∈ Finset.range n, x^k) = 1 - x^n := by
  rw [mul_comm, geom_sum_mul_neg]

/-- **Golod–Shafarevich generating function bound** (finite, tail-free form). -/
theorem gs_gen_bound (c r M N : ℕ) (b t : ℕ → ℕ) (hN : M + 2 ≤ N)
    (hbzero : ∀ j, M ≤ j → b j = 0)
    (ht0 : t 0 = 0)
    (ht : ∀ k, t (k+1) ≤ r * gsig b k)
    (hrec : ∀ k, c * gsig b k + 1 = gsig b (k+1) + t k)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    0 < (∑ j ∈ Finset.range M, (b j : ℝ) * x^j) * (1 - (c:ℝ)*x + (r:ℝ)*x^2) := by
  have hN2 : 2 ≤ N := by omega
  set Bp : ℝ := ∑ j ∈ Finset.range M, (b j : ℝ) * x^j with hBp
  have hBpnn : 0 ≤ Bp := by
    rw [hBp]; exact Finset.sum_nonneg (fun j _ => by positivity)
  set SP : ℝ := ∑ k ∈ Finset.range N, (gsig b k : ℝ) * x^k with hSP
  set SG : ℝ := ∑ k ∈ Finset.range N, x^k with hSG
  set SQ : ℝ := ∑ k ∈ Finset.range N, (gsig b (k+1) : ℝ) * x^k with hSQ
  set SQ2 : ℝ := ∑ m ∈ Finset.range (N+1), (gsig b m : ℝ) * x^m with hSQ2
  set SR : ℝ := ∑ k ∈ Finset.range (N-1), (gsig b k : ℝ) * x^k with hSR
  -- ### step 1
  have hsplit : (∑ k ∈ Finset.range N,
      ((c:ℝ) * (gsig b k : ℝ) + 1 - (gsig b (k+1) : ℝ)) * x^k) = (c:ℝ)*SP + SG - SQ := by
    rw [hSP, hSG, hSQ]
    have hrw : (∑ k ∈ Finset.range N,
        ((c:ℝ) * (gsig b k : ℝ) + 1 - (gsig b (k+1) : ℝ)) * x^k)
        = ∑ k ∈ Finset.range N,
          ((c:ℝ) * ((gsig b k : ℝ) * x^k) + x^k - (gsig b (k+1) : ℝ) * x^k) :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [hrw]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hstep1 : (∑ k ∈ Finset.range N,
      ((c:ℝ) * (gsig b k : ℝ) + 1 - (gsig b (k+1) : ℝ)) * x^k)
      = ∑ k ∈ Finset.range N, (t k : ℝ) * x^k := by
    apply Finset.sum_congr rfl
    intro k _
    have hk : (c:ℝ) * (gsig b k : ℝ) + 1 = (gsig b (k+1) : ℝ) + (t k : ℝ) := by
      exact_mod_cast hrec k
    rw [hk]; ring
  have hstep2 : (∑ k ∈ Finset.range N, (t k : ℝ) * x^k) ≤ (r:ℝ) * x * SR := by
    have hreindex : (∑ k ∈ Finset.range N, (t k : ℝ) * x^k)
        = ∑ k ∈ Finset.range (N-1), (t (k+1) : ℝ) * x^(k+1) := by
      have h : N = (N - 1) + 1 := by omega
      conv_lhs => rw [h, Finset.sum_range_succ']
      rw [ht0]; simp
    rw [hreindex]
    have hSR' : (r:ℝ) * x * SR
        = ∑ k ∈ Finset.range (N-1), (r:ℝ) * (gsig b k : ℝ) * x^(k+1) := by
      rw [hSR, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hSR']
    apply Finset.sum_le_sum
    intro k _
    have hcast : (t (k+1) : ℝ) ≤ (r:ℝ) * (gsig b k : ℝ) := by exact_mod_cast ht k
    have hxnn : (0:ℝ) ≤ x^(k+1) := by positivity
    calc (t (k+1) : ℝ) * x^(k+1) ≤ ((r:ℝ) * (gsig b k : ℝ)) * x^(k+1) :=
          mul_le_mul_of_nonneg_right hcast hxnn
      _ = (r:ℝ) * (gsig b k : ℝ) * x^(k+1) := by ring
  have hstep : (∑ k ∈ Finset.range N,
      ((c:ℝ) * (gsig b k : ℝ) + 1 - (gsig b (k+1) : ℝ)) * x^k) ≤ (r:ℝ) * x * SR := by
    rw [hstep1]; exact hstep2
  -- ### step 2: identities
  have hSPid : (1 - x) * SP
      = (∑ j ∈ Finset.range N, (b j : ℝ) * x^j) - (gsig b (N-1) : ℝ) * x^N := by
    rw [hSP]
    have h := geom_gsig b x (N-1)
    rwa [show N - 1 + 1 = N from by omega] at h
  have hSGid : (1 - x) * SG = 1 - x^N := by
    rw [hSG]; exact geom_shift x N
  have hSQid : x * SQ = SQ2 - (gsig b 0 : ℝ) := by
    rw [hSQ, hSQ2, Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range N, x * ((gsig b (k+1) : ℝ) * x^k))
        = ∑ k ∈ Finset.range N, (gsig b (k+1) : ℝ) * x^(k+1) from by
          apply Finset.sum_congr rfl; intro k _; ring]
    rw [Finset.sum_range_succ']
    ring
  have hSQ2id : (1 - x) * SQ2 = (∑ j ∈ Finset.range (N+1), (b j : ℝ) * x^j)
      - (gsig b N : ℝ) * (x^N * x) := by
    rw [hSQ2]
    have h := geom_gsig b x N
    rwa [pow_succ] at h
  have hSRid : (1 - x) * SR
      = (∑ j ∈ Finset.range (N-1), (b j : ℝ) * x^j) - (gsig b (N-2) : ℝ) * x^(N-1) := by
    rw [hSR]
    have h := geom_gsig b x (N-2)
    rwa [show N - 2 + 1 = N - 1 from by omega] at h
  have hxSR : x * SR = ∑ k ∈ Finset.range (N-1), (gsig b k : ℝ) * x^(k+1) := by
    rw [hSR, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  have hSR3id : (1 - x) * (∑ k ∈ Finset.range (N-1), (gsig b k : ℝ) * x^(k+1))
      = (∑ j ∈ Finset.range (N-1), (b j : ℝ) * x^(j+1)) - (gsig b (N-2) : ℝ) * x^N := by
    have h1 : (∑ k ∈ Finset.range (N-1), (gsig b k : ℝ) * x^(k+1))
        = x * (∑ k ∈ Finset.range (N-1), (gsig b k : ℝ) * x^k) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [h1]
    rw [show (1 - x) * (x * (∑ k ∈ Finset.range (N-1), (gsig b k : ℝ) * x^k))
        = x * ((1 - x) * (∑ k ∈ Finset.range (N-1), (gsig b k : ℝ) * x^k)) from by ring]
    have h := geom_gsig b x (N-2)
    rw [show N - 2 + 1 = N - 1 from by omega] at h
    rw [h, mul_sub]
    congr 1
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    · have hp : x * x^(N-1) = x^N := by
        rw [mul_comm, ← pow_succ]; congr 1; omega
      calc x * ((gsig b (N-2) : ℝ) * x^(N-1))
          = (gsig b (N-2) : ℝ) * (x * x^(N-1)) := by ring
        _ = (gsig b (N-2) : ℝ) * x^N := by rw [hp]
  -- tails
  have htail : ∀ L : ℕ, M ≤ L → (∑ j ∈ Finset.range L, (b j : ℝ) * x^j) = Bp := by
    intro L hL
    rw [hBp]
    conv_lhs => rw [show L = M + (L - M) from by omega]
    rw [Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range (L - M), (b (M+i) : ℝ) * x^(M+i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hbzero (M+i) (by omega)]
      simp
    rw [hz, add_zero]
  have htail1 : ∀ L : ℕ, M ≤ L → (∑ j ∈ Finset.range L, (b j : ℝ) * x^(j+1)) = Bp * x := by
    intro L hL
    have h1 : (∑ j ∈ Finset.range L, (b j : ℝ) * x^(j+1))
        = x * (∑ j ∈ Finset.range L, (b j : ℝ) * x^j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [h1, htail L hL]; ring
  -- multiply and rewrite
  have hpos : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt hpos)
  have hL : x*(1-x)*(∑ k ∈ Finset.range N,
      ((c:ℝ) * (gsig b k : ℝ) + 1 - (gsig b (k+1) : ℝ)) * x^k)
      = (c:ℝ)*(x*((1-x)*SP)) + x*((1-x)*SG) - ((1-x)*(x*SQ)) := by
    rw [hsplit]; ring
  have hR : x*(1-x)*((r:ℝ)*x*SR) = (r:ℝ)*x*((1-x)*(x*SR)) := by ring
  have hmulsq : (1 - x) * (SQ2 - (gsig b 0 : ℝ))
      = (1 - x) * SQ2 - (1 - x) * (gsig b 0 : ℝ) := by ring
  rw [hL, hR] at hmul
  rw [hSPid, hSGid, hSQid, hmulsq, hSQ2id, hxSR, hSR3id] at hmul
  rw [htail N (by omega), htail (N+1) (by omega), htail1 (N-1) (by omega)] at hmul
  -- side conditions
  have hrecR : (c:ℝ) * (gsig b (N-1) : ℝ) + 1 = (gsig b N : ℝ) + (t (N-1) : ℝ) := by
    have h := hrec (N-1)
    rw [show N - 1 + 1 = N from by omega] at h
    exact_mod_cast h
  have hcastR : (t (N-1) : ℝ) ≤ (r:ℝ) * (gsig b (N-2) : ℝ) := by
    have h := ht (N-2)
    have h2 : N - 2 + 1 = N - 1 := by omega
    rw [h2] at h
    exact_mod_cast h
  have hs0 : (0:ℝ) ≤ (gsig b 0 : ℝ) := by positivity
  have hE : x + (gsig b 0 : ℝ)*(1-x) + (x^N*x)*((r:ℝ)*(gsig b (N-2) : ℝ) - (t (N-1) : ℝ))
      ≤ Bp * (1 - (c:ℝ)*x + (r:ℝ)*x^2) := by
    rw [pow_two]
    have hrecR2 := congrArg (fun u : ℝ => (x^N*x)*u) hrecR
    nlinarith [hmul, hrecR2]
  have hEx : x ≤ x + (gsig b 0 : ℝ)*(1-x)
      + (x^N*x)*((r:ℝ)*(gsig b (N-2) : ℝ) - (t (N-1) : ℝ)) := by
    have h1 : 0 ≤ (x^N*x)*((r:ℝ)*(gsig b (N-2) : ℝ) - (t (N-1) : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ (gsig b 0 : ℝ)*(1-x) := mul_nonneg hs0 (by linarith)
    linarith
  have hfin : 0 < Bp * (1 - (c:ℝ)*x + (r:ℝ)*x^2) := lt_of_lt_of_le hx0 (le_trans hEx hE)
  rwa [hBp] at hfin



theorem quad_final (c r : ℕ) (hc0 : 0 < c) (hcr : c ≤ r)
    (hq : ∀ x : ℝ, 0 < x → x < 1 → 0 < 1 - (c:ℝ)*x + (r:ℝ)*x^2) :
    c * c < 4 * r := by
  have hr1 : 1 ≤ r := le_trans hc0 hcr
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hcr' : c < 2 * r := by omega
  set x : ℝ := (c:ℝ)/(2*(r:ℝ)) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x < 1 := by
    rw [hx, div_lt_one (by positivity : (0:ℝ) < 2*(r:ℝ))]
    exact_mod_cast hcr'
  have h := hq x hx0 hx1
  rw [hx] at h
  have key : (1:ℝ) - (c:ℝ)*((c:ℝ)/(2*(r:ℝ))) + (r:ℝ)*(((c:ℝ)/(2*(r:ℝ)))^2)
      = 1 - (c:ℝ)^2/(4*(r:ℝ)) := by
    field_simp
    ring
  rw [key] at h
  have h2 : (c:ℝ)*(c:ℝ) < 4*(r:ℝ) := by
    have hsplit := (div_lt_one (by positivity : (0:ℝ) < 4*(r:ℝ))).mp (sub_pos.mp h)
    rw [pow_two] at hsplit
    linarith
  exact_mod_cast h2




end GSGen

namespace ScratchSerre

variable {K B : Type*} [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]

/-- **Exact sequences give additivity of dimension** over a field. -/
lemma finrank_eq_add_of_exact {A C : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : LinearMap.range f = LinearMap.ker g) :
    finrank K B = finrank K A + finrank K C := by
  have hle : finrank K B ≤ finrank K A + finrank K C := finrank_le_add_of_exact f g h
  have hker : finrank K ↥(LinearMap.ker g) = finrank K A := by
    rw [← h, LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hf)]
  have hq : finrank K (B ⧸ LinearMap.ker g) = finrank K C := by
    rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange g), LinearMap.range_eq_top.mpr hg,
      finrank_top]
  have h4 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
  omega

/-- **Dimension of a product of quotients.** For submodules `p i ≤ M i`,
`dim ((∀ i, M i) ⧸ ∏ i, p i) = ∑ i, dim (M i ⧸ p i)`. -/
lemma finrank_pi_quotient {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)]
    (p : ∀ i, Submodule K (M i)) :
    finrank K ((∀ i, M i) ⧸ Submodule.pi Set.univ p) = ∑ i, finrank K (M i ⧸ p i) := by
  rw [LinearEquiv.finrank_eq (Submodule.quotientPi (Ms := M) p), Module.finrank_pi_fintype]

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α]

/-- `x - algebraMap (augB x)` lies in the ideal spanned by the elements `of g - 1`. -/
lemma sub_algebraMap_augB_mem_span (x : MonoidAlgebra (ZMod p) G) :
    x - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G x) ∈
      Ideal.span (Set.range (fun g : G => MonoidAlgebra.of (ZMod p) G g - 1)) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      rw [augB_of, map_one]
      simpa using Ideal.subset_span (Set.mem_range_self g)
  | add x y hx hy =>
      have h : augB p G (x + y) = augB p G x + augB p G y := map_add _ _ _
      rw [h, map_add]
      have hxy : x + y - (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G x) +
          algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G y)) =
          (x - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G x)) +
          (y - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G y)) := by abel
      rw [hxy]
      exact Ideal.add_mem _ hx hy
  | smul c x hx =>
      have hc : augB p G (c • x) = c * augB p G x := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes]
        rfl
      have key : c • x - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G (c • x)) =
          c • (x - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G x)) := by
        rw [hc, map_mul, smul_sub, Algebra.smul_def, Algebra.smul_def]
      rw [key, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hx

/-- The augmentation ideal is spanned by the elements `of g - 1`. -/
lemma bG_eq_span_sub_one :
    bG p G = Ideal.span (Set.range (fun g : G => MonoidAlgebra.of (ZMod p) G g - 1)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [bG, RingHom.mem_ker] at hx
    have hx' : augB p G x = 0 := hx
    have h : x = x - algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (augB p G x) := by
      rw [hx', map_zero, sub_zero]
    rw [h]
    exact sub_algebraMap_augB_mem_span p G x
  · rw [Ideal.span_le]
    rintro x ⟨g, rfl⟩
    show MonoidAlgebra.of (ZMod p) G g - 1 ∈ bG p G
    rw [show bG p G = RingHom.ker (augB p G).toRingHom from rfl, RingHom.mem_ker]
    change augB p G (MonoidAlgebra.of (ZMod p) G g - 1) = 0
    rw [map_sub, augB_of, map_one, sub_self]

/-- Every `of g - 1` lies in the span of the `tG i` when `π` is surjective. -/
lemma sub_one_mem_span_tG (π : FreeGroup α →* G) (hπ : Function.Surjective π) (g : G) :
    MonoidAlgebra.of (ZMod p) G g - 1 ∈ Ideal.span (Set.range (fun i : α => tG p G α π i)) := by
  obtain ⟨y, rfl⟩ := hπ g
  have h1 : rho p α π (ScratchGS.F p α y) =
      ∑ i, rho p α π (ScratchGS.Dfun p α i y) * tG p G α π i := by
    rw [ScratchGS.F, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, rho_t]
  have h2 : rho p α π (ScratchGS.F p α y) = MonoidAlgebra.of (ZMod p) G (π y) - 1 := by
    rw [ScratchGS.fox_group, map_sub, rho_of, map_one]
  rw [← h2, h1]
  exact Ideal.sum_mem _ (fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

/-- **The augmentation ideal is spanned by the images of the generators** (for `π` surjective). -/
lemma bG_eq_span_tG (π : FreeGroup α →* G) (hπ : Function.Surjective π) :
    Ideal.span (Set.range (fun i : α => tG p G α π i)) = bG p G := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact tG_mem_bG p G α π i
  · rw [bG_eq_span_sub_one p G, Ideal.span_le]
    rintro x ⟨g, rfl⟩
    exact sub_one_mem_span_tG p G α π hπ g

variable [Fintype G]

/-- **Item 1.** `dim ((α → B) ⧸ ∏ᵢ b^n) = card α * dim (B ⧸ b^n)`. -/
lemma finrank_quot_pi_pow (n : ℕ) :
    finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸
        Submodule.pi Set.univ
          (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ (n + 1)))) =
      Fintype.card α * finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (bG p G ^ (n + 1))) := by
  rw [finrank_pi_quotient (K := ZMod p) (M := fun _ : α => MonoidAlgebra (ZMod p) G)
    (fun _ => Submodule.restrictScalars (ZMod p) (bG p G ^ (n + 1)))]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Every element of the augmentation ideal is `Phi q` for some `q` (for `π` surjective). -/
lemma exists_Phi_eq (π : FreeGroup α →* G) (hπ : Function.Surjective π) {x : MonoidAlgebra (ZMod p) G}
    (hx : x ∈ bG p G) : ∃ q : α → MonoidAlgebra (ZMod p) G, Phi p G α π q = ⟨x, hx⟩ := by
  have hspan : Submodule.span (MonoidAlgebra (ZMod p) G)
      (Set.range (fun i : α => tG p G α π i)) = bG p G := by
    rw [← bG_eq_span_tG p G α π hπ]
  have hx' : x ∈ Submodule.span (MonoidAlgebra (ZMod p) G)
      (Set.range (fun i : α => tG p G α π i)) := by
    rw [hspan]; exact hx
  let P : (z : MonoidAlgebra (ZMod p) G) → Prop := fun z =>
    ∀ hz : z ∈ bG p G, ∃ q : α → MonoidAlgebra (ZMod p) G, Phi p G α π q = ⟨z, hz⟩
  have key : ∀ z ∈ Submodule.span (MonoidAlgebra (ZMod p) G)
      (Set.range (fun i : α => tG p G α π i)), P z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => P z) ?_ ?_ ?_ ?_ hz
    · rintro w ⟨i, rfl⟩ hw
      refine ⟨fun j => if j = i then 1 else 0, Subtype.ext ?_⟩
      show ∑ j, (if j = i then (1 : MonoidAlgebra (ZMod p) G) else 0) * tG p G α π j = tG p G α π i
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul]
      · intro j _ hj; rw [if_neg hj, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · intro h0
      exact ⟨0, Subtype.ext (by simp)⟩
    · intro u v hu hv huP hvP hmem
      rcases huP (hspan ▸ hu) with ⟨q, hq⟩
      rcases hvP (hspan ▸ hv) with ⟨q', hq'⟩
      refine ⟨q + q', Subtype.ext ?_⟩
      rw [map_add]
      show ∑ i, q i * tG p G α π i + ∑ i, q' i * tG p G α π i = u + v
      have hqval : ∑ i, q i * tG p G α π i = u := by
        simpa [Phi] using congrArg Subtype.val hq
      have hq'val : ∑ i, q' i * tG p G α π i = v := by
        simpa [Phi] using congrArg Subtype.val hq'
      rw [hqval, hq'val]
    · intro a u hu huP hmem
      rcases huP (hspan ▸ hu) with ⟨q, hq⟩
      refine ⟨fun i => a * q i, Subtype.ext ?_⟩
      have hqval : ∑ i, q i * tG p G α π i = u := by
        simpa [Phi] using congrArg Subtype.val hq
      show ∑ i, (a * q i) * tG p G α π i = a * u
      rw [← hqval, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [mul_assoc])
  exact key x hx' hx

/-- **`Phi` is surjective** onto the augmentation ideal, for `π` surjective. -/
lemma Phi_range_eq_top (π : FreeGroup α →* G) (hπ : Function.Surjective π) :
    LinearMap.range (Phi p G α π) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  exact exists_Phi_eq p G α π hπ x.2

/-- The composite of `Phi` with the inclusion of the augmentation ideal into `B`. -/
noncomputable def Phi' (π : FreeGroup α →* G) :
    (α → MonoidAlgebra (ZMod p) G) →ₗ[ZMod p] MonoidAlgebra (ZMod p) G :=
  ((Submodule.subtype (bG p G)).restrictScalars (ZMod p)).comp (Phi p G α π)

lemma Phi'_apply (π : FreeGroup α →* G) (q : α → MonoidAlgebra (ZMod p) G) :
    Phi' p G α π q = ∑ i, q i * tG p G α π i := by
  simp [Phi', Phi]

/-- The range of `Φ'` is the augmentation ideal. -/
lemma range_Phi' (π : FreeGroup α →* G) (hπ : Function.Surjective π) :
    LinearMap.range (Phi' p G α π) =
      Submodule.restrictScalars (ZMod p) (bG p G) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨q, rfl⟩
    rw [Phi'_apply]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (tG_mem_bG p G α π i))
  · intro y hy
    obtain ⟨q, hq⟩ := exists_Phi_eq p G α π hπ hy
    exact ⟨q, by rw [Phi'_apply]; exact congrArg Subtype.val hq⟩

/-- The Koszul-type map `(α → B) → B ⧸ b^(n+1)`. -/
noncomputable def Psi (π : FreeGroup α →* G) (n : ℕ) :
    (α → MonoidAlgebra (ZMod p) G) →ₗ[ZMod p]
      (MonoidAlgebra (ZMod p) G ⧸ bG p G ^ (n + 1)) :=
  ((Submodule.mkQ (bG p G ^ (n + 1))).restrictScalars (ZMod p)).comp (Phi' p G α π)

lemma Psi_apply (π : FreeGroup α →* G) (n : ℕ) (q : α → MonoidAlgebra (ZMod p) G) :
    Psi p G α π n q = Submodule.Quotient.mk (Phi' p G α π q) := by
  simp [Psi]

/-- `∏ᵢ b^n ⊆ ker Ψ`. -/
lemma pi_pow_le_ker_Psi (π : FreeGroup α →* G) (n : ℕ) :
    Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n)) ≤
      LinearMap.ker (Psi p G α π n) := by
  intro q hq
  rw [LinearMap.mem_ker, Psi_apply, Submodule.Quotient.mk_eq_zero, Phi'_apply]
  have hqi : ∀ i, q i ∈ bG p G ^ n := fun i =>
    (Submodule.mem_pi.mp hq) i (Set.mem_univ i)
  refine Ideal.sum_mem _ (fun i _ => ?_)
  rw [Submodule.pow_succ]
  exact Ideal.mul_mem_mul (hqi i) (tG_mem_bG p G α π i)

/-- `ker Φ ⊆ ker Ψ`. -/
lemma ker_Phi_le_ker_Psi (π : FreeGroup α →* G) (n : ℕ) :
    LinearMap.ker (Phi p G α π) ≤ LinearMap.ker (Psi p G α π n) := by
  intro q hq
  rw [LinearMap.mem_ker, Psi_apply, Submodule.Quotient.mk_eq_zero]
  rw [Phi'_apply]
  have hqval : ∑ i, q i * tG p G α π i = 0 := by
    have h := congrArg (fun x : ↥(bG p G) => (x : MonoidAlgebra (ZMod p) G)) hq
    simpa [Phi, Submodule.coe_zero] using h
  rw [hqval]
  exact Submodule.zero_mem _

/-- `Φ'` maps `∏ᵢ b^n` onto `b^(n+1)`. -/
lemma map_Phi'_pi (π : FreeGroup α →* G) (hπ : Function.Surjective π) (n : ℕ) :
    Submodule.map (Phi' p G α π)
        (Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n))) =
      Submodule.restrictScalars (ZMod p) (bG p G ^ (n + 1)) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨q, hq, rfl⟩
    rw [Phi'_apply]
    have hqi : ∀ i, q i ∈ bG p G ^ n := fun i => (Submodule.mem_pi.mp hq) i (Set.mem_univ i)
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [Submodule.pow_succ]
    exact Ideal.mul_mem_mul (hqi i) (tG_mem_bG p G α π i)
  · intro y hy
    have hyB : y ∈ bG p G ^ n * bG p G := by
      rw [← Submodule.pow_succ]; exact hy
    refine Submodule.mul_induction_on
      (C := fun r => r ∈ Submodule.map (Phi' p G α π)
        (Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n))))
      hyB ?_ ?_
    · intro m hm n' hn'
      have hn'' : n' ∈ LinearMap.range (Phi' p G α π) := by
        rw [range_Phi' p G α π hπ]; exact hn'
      obtain ⟨q, hq⟩ := hn''
      refine ⟨fun i => m * q i, ?_, ?_⟩
      · refine Submodule.mem_pi.mpr (fun i _ => ?_)
        have h2 : m * q i ∈ bG p G ^ n * ⊤ :=
          Ideal.mul_mem_mul hm (Submodule.mem_top)
        rwa [Ideal.mul_top] at h2
      · rw [Phi'_apply]
        show ∑ i, (m * q i) * tG p G α π i = m * n'
        rw [← hq, Phi'_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_assoc])
    · intro x z hx hz
      rcases hx with ⟨q, hq, rfl⟩
      rcases hz with ⟨q', hq', rfl⟩
      exact ⟨q + q', Submodule.add_mem _ hq hq', by rw [map_add]⟩

/-- `ker Ψ ⊆ ker Φ ⊔ ∏ᵢ b^n`. -/
lemma ker_Psi_le (π : FreeGroup α →* G) (hπ : Function.Surjective π) (n : ℕ) :
    LinearMap.ker (Psi p G α π n) ≤ LinearMap.ker (Phi p G α π) ⊔
      Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n)) := by
  intro q hq
  rw [LinearMap.mem_ker, Psi_apply, Submodule.Quotient.mk_eq_zero] at hq
  have hq' : Phi' p G α π q ∈ Submodule.map (Phi' p G α π)
      (Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n))) := by
    rw [map_Phi'_pi p G α π hπ n]; exact hq
  obtain ⟨q₀, hq₀, hqq₀⟩ := hq'
  have hker : Phi p G α π (q - q₀) = 0 := by
    have h1 : Phi' p G α π (q - q₀) = 0 := by rw [map_sub, hqq₀, sub_self]
    have h2 : ((Phi p G α π (q - q₀) : ↥(bG p G)) : MonoidAlgebra (ZMod p) G) = 0 := by
      simpa [Phi', Submodule.coe_zero] using h1
    refine Subtype.ext ?_
    rw [Submodule.coe_zero]
    exact h2
  rw [← sub_add_cancel q q₀]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hker) (Submodule.mem_sup_right hq₀)

/-- The kernel of `Ψ` is `ker Φ ⊔ ∏ᵢ b^n`. -/
lemma ker_Psi_eq (π : FreeGroup α →* G) (hπ : Function.Surjective π) (n : ℕ) :
    LinearMap.ker (Psi p G α π n) = LinearMap.ker (Phi p G α π) ⊔
      Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n)) := by
  refine le_antisymm (ker_Psi_le p G α π hπ n) ?_
  exact sup_le (ker_Phi_le_ker_Psi p G α π n) (pi_pow_le_ker_Psi p G α π n)

/-- The range of `Ψ` is the image of the augmentation ideal in `B ⧸ b^(n+1)`. -/
lemma range_Psi (π : FreeGroup α →* G) (hπ : Function.Surjective π) (n : ℕ) :
    LinearMap.range (Psi p G α π n) =
      (Submodule.map (Submodule.mkQ (bG p G ^ (n + 1))) (bG p G)).restrictScalars (ZMod p) := by
  rw [Psi, LinearMap.range_comp, range_Phi' p G α π hπ]
  rfl

/-- `B ⧸ b` is one-dimensional. -/
lemma finrank_quot_bG :
    finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸ bG p G) = 1 := by
  have hsurj : Function.Surjective (augB p G).toLinearMap := fun c =>
    ⟨algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) c, by
      rw [AlgHom.toLinearMap_apply, AlgHom.commutes, Algebra.algebraMap_self_apply]⟩
  have h : LinearMap.ker (augB p G).toLinearMap = Submodule.restrictScalars (ZMod p) (bG p G) := rfl
  have key : finrank (ZMod p)
      (MonoidAlgebra (ZMod p) G ⧸ Submodule.restrictScalars (ZMod p) (bG p G)) = 1 := by
    rw [← h, LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (augB p G).toLinearMap),
      LinearMap.range_eq_top.mpr hsurj, finrank_top]
    exact Module.finrank_self (ZMod p)
  exact key

/-- **Item 2.** `dim ((α → B) ⧸ Q n) = dim (B ⧸ b^(n+1)) - 1`. -/
lemma finrank_quot_Q (π : FreeGroup α →* G) (hπ : Function.Surjective π) (n : ℕ) :
    finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ (LinearMap.ker (Phi p G α π) ⊔
        Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n)))) =
      finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (bG p G ^ (n + 1))) - 1 := by
  rw [← ker_Psi_eq p G α π hπ n]
  rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (Psi p G α π n))]
  rw [range_Psi p G α π hπ n]
  exact finrank_image_mkQ_pow_eq_sub_one (K := ZMod p) (B := MonoidAlgebra (ZMod p) G)
    (bG p G) n (finrank_quot_bG p G)

/-- **`ker Φ = range dRel`**: the Fox resolution is exact at `(α → B)`. -/
lemma ker_Phi_eq_range_dRel (rel : Finset (FreeGroup α)) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) :
    LinearMap.ker (Phi p G α π) = LinearMap.range (dRel p α G rel π) := by
  refine le_antisymm (ker_Phi_le_range_dRel (p := p) (α := α) (G := G) rel π hπ hrel) ?_
  rintro _ ⟨f, rfl⟩
  exact Phi_dRel_eq_zero (p := p) (α := α) (G := G) rel π hπ hrel f

/-- **Fox product rule**: `D_i (x * y) = aug y • D_i x + x • D_i y`. -/
lemma Dlin_mul (i : α) (x y : ScratchGS.W p α) :
    ScratchGS.Dlin p α i (x * y) =
      ScratchGS.aug p α y • ScratchGS.Dlin p α i x + x * ScratchGS.Dlin p α i y := by
  induction y using MonoidAlgebra.induction_on with
  | of g =>
      rw [ScratchGS.aug_of, one_smul]
      exact ScratchGS.Dlin_mul_of p α i x g
  | add y z hy hz =>
      rw [mul_add, map_add, hy, hz, map_add, map_add, add_smul, mul_add]
      abel
  | smul c y hy =>
      rw [mul_smul_comm, map_smul, map_smul, hy, smul_add]
      rw [map_smul, ← smul_assoc, ← mul_smul_comm]

/-- **The Fox derivative shifts the augmentation filtration by one**: `D_i(IW^(k+1)) ⊆ IW^k`. -/
lemma Dlin_mem_IW_pow_succ (i : α) : ∀ k : ℕ, ∀ {z : ScratchGS.W p α},
    z ∈ ScratchGS.IW p α ^ (k + 1) → ScratchGS.Dlin p α i z ∈ ScratchGS.IW p α ^ k := by
  let J : Submodule (ScratchGS.W p α) (ScratchGS.W p α) := ScratchGS.IW p α
  have hJ : J = ScratchGS.IW p α := rfl
  have htwo : Ideal.IsTwoSided J := by
    refine Ideal.IsTwoSided.mk (fun b ha => ?_)
    rw [hJ, ScratchGS.mem_IW_iff] at ha ⊢
    rw [map_mul, ha, zero_mul]
  intro k
  induction k with
  | zero =>
      intro z _
      rw [Submodule.pow_zero]
      simp
  | succ k ih =>
      intro z hz
      change z ∈ J ^ (k + 1 + 1) at hz
      rw [show J ^ (k + 1 + 1) = J * J ^ (k + 1) from
        Submodule.pow_succ' (J) (by omega : k + 1 ≠ 0)] at hz
      change ScratchGS.Dlin p α i z ∈ J ^ (k + 1)
      refine Submodule.mul_induction_on
        (C := fun r => ScratchGS.Dlin p α i r ∈ J ^ (k + 1)) hz ?_ ?_
      · intro a ha b hb
        rw [Dlin_mul]
        have hbIW : b ∈ ScratchGS.IW p α := Ideal.pow_le_self (by omega : k + 1 ≠ 0) (hJ ▸ hb)
        have hb0 : ScratchGS.aug p α b = 0 := (ScratchGS.mem_IW_iff p α b).mp hbIW
        rw [hb0, zero_smul, zero_add]
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · subst h0
          rw [show J ^ (0 + 1) = J from Submodule.pow_one J]
          exact htwo.mul_mem_of_left _ ha
        · rw [show J ^ (k + 1) = J * J ^ k from
            Submodule.pow_succ' (J) (by omega : k ≠ 0)]
          exact Submodule.mul_mem_mul ha (show ScratchGS.Dlin p α i b ∈ J ^ k from ih (hJ ▸ hb))
      · intro u v hu hv
        rw [map_add]
        exact Submodule.add_mem _ hu hv

/-- `augB ∘ rho = aug`. -/
lemma augB_rho (π : FreeGroup α →* G) (z : ScratchGS.W p α) :
    augB p G (rho p α π z) = ScratchGS.aug p α z := by
  induction z using MonoidAlgebra.induction_on with
  | of g => rw [rho_of, augB_of, ScratchGS.aug_of]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

/-- **`rho` maps the augmentation ideal into the augmentation ideal.** -/
lemma rho_mem_bG (π : FreeGroup α →* G) {z : ScratchGS.W p α}
    (hz : z ∈ ScratchGS.IW p α) : rho p α π z ∈ bG p G := by
  rw [bG, RingHom.mem_ker]
  change augB p G (rho p α π z) = 0
  rw [augB_rho, (ScratchGS.mem_IW_iff p α z).mp hz]

/-- Relators have order `≥ 2`: `kappa r ∈ IW²`. -/
lemma kappa_mem_IW_sq (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    {r : FreeGroup α} (hr : r ∈ (rel : Set (FreeGroup α))) :
    kappa p α r ∈ ScratchGS.IW p α ^ 2 := by
  have hrker : r ∈ π.ker := by
    rw [← hrel]
    exact Subgroup.subset_normalClosure hr
  have h := sub_one_mem_gsIW_sq_of_mem_ker (p := p) (α := α) (G := G) hG π hπ hgen hrker
  have hIW : gsIW p α = ScratchGS.IW p α := rfl
  rw [hIW] at h
  simpa [kappa] using h

/-- **Input II**: `rho (Dlin i (kappa r)) ∈ bG` for `r ∈ rel`. -/
lemma rho_Dlin_kappa_mem_bG (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    {r : FreeGroup α} (hr : r ∈ (rel : Set (FreeGroup α))) (i : α) :
    rho p α π (ScratchGS.Dlin p α i (kappa p α r)) ∈ bG p G := by
  have hmem := Dlin_mem_IW_pow_succ p α i (k := 1) (kappa_mem_IW_sq p G α hG π hπ hgen hrel hr)
  rw [Submodule.pow_one (ScratchGS.IW p α)] at hmem
  exact rho_mem_bG p G α π hmem

/-- **Well-definedness of the relation count**: `dRel` maps `∏ᵢ b^m` into `∏ᵢ b^(m+1)`. -/
lemma dRel_mem_pi_pow (hG : IsPGroup p G) (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    (m : ℕ) {f : rel → MonoidAlgebra (ZMod p) G}
    (hf : f ∈ Submodule.pi Set.univ
      (fun _ : rel => Submodule.restrictScalars (ZMod p) (bG p G ^ m))) :
    dRel p α G rel π f ∈ Submodule.pi Set.univ
      (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ (m + 1))) := by
  rw [Submodule.mem_pi]
  intro i _
  show (∑ r : rel, f r * rho p α π (ScratchGS.Dlin p α i (kappa p α (r : FreeGroup α)))) ∈
    Submodule.restrictScalars (ZMod p) (bG p G ^ (m + 1))
  rw [Submodule.pow_succ]
  refine Ideal.sum_mem _ (fun r _ => ?_)
  exact Ideal.mul_mem_mul ((Submodule.mem_pi.mp hf) r (Set.mem_univ r))
    (rho_Dlin_kappa_mem_bG p G α hG π hπ hgen hrel r.2 i)

/-- `P n = ∏ᵢ bG^n`. -/
abbrev Ppow (n : ℕ) : Submodule (ZMod p) (α → MonoidAlgebra (ZMod p) G) :=
  Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (bG p G ^ n))

/-- `Q n = ker Φ ⊔ P n`. -/
abbrev Qker (π : FreeGroup α →* G) (n : ℕ) :
    Submodule (ZMod p) (α → MonoidAlgebra (ZMod p) G) :=
  LinearMap.ker (Phi p G α π) ⊔ Ppow p G α n

/-- The induced map `(rel → B) → (α → B) ⧸ P n` sending `f` to the class of `dRel f`. -/
noncomputable def psi (π : FreeGroup α →* G) (rel : Finset (FreeGroup α)) (n : ℕ) :
    (rel → MonoidAlgebra (ZMod p) G) →ₗ[ZMod p]
      ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α n) :=
  ((Submodule.mkQ (Ppow p G α n)).restrictScalars (ZMod p)).comp (dRel p α G rel π)

lemma psi_apply (π : FreeGroup α →* G) (rel : Finset (FreeGroup α)) (n : ℕ)
    (f : rel → MonoidAlgebra (ZMod p) G) :
    psi p G α π rel n f = Submodule.Quotient.mk (dRel p α G rel π f) := by
  simp [psi]

/-- The image of `ψ` is `Q n ⧸ P n`. -/
lemma range_psi (π : FreeGroup α →* G) (rel : Finset (FreeGroup α)) (hπ : Function.Surjective π)
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) (n : ℕ) :
    LinearMap.range (psi p G α π rel n) =
      Submodule.map (Submodule.mkQ (Ppow p G α n)) (Qker p G α π n) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨f, rfl⟩
    refine ⟨dRel p α G rel π f, ?_, ?_⟩
    · exact Submodule.mem_sup_left (by
        rw [ker_Phi_eq_range_dRel p G α rel π hπ hrel]
        exact ⟨f, rfl⟩)
    · rw [Submodule.mkQ_apply, psi_apply]
  · rintro y ⟨q, hq, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hq
    rw [map_add, Submodule.mkQ_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero (Ppow p G α n)).mpr hb, add_zero]
    have ha' : a ∈ LinearMap.range (dRel p α G rel π) := by
      rw [← ker_Phi_eq_range_dRel p G α rel π hπ hrel]
      exact ha
    obtain ⟨f, rfl⟩ := ha'
    exact ⟨f, by rw [psi_apply]⟩

/-- `∏ᵢ b^(n-1) ⊆ ker ψ` (for `n ≥ 1`). -/
lemma dRel_pi_le_ker_psi (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker)
    {n : ℕ} (hn : 1 ≤ n) :
    Submodule.pi Set.univ (fun _ : rel => Submodule.restrictScalars (ZMod p) (bG p G ^ (n - 1))) ≤
      LinearMap.ker (psi p G α π rel n) := by
  intro f hf
  rw [LinearMap.mem_ker, psi_apply, Submodule.Quotient.mk_eq_zero]
  have h := dRel_mem_pi_pow p G α hG π hπ hgen hrel (n - 1) hf
  rwa [Nat.sub_add_cancel (m := 1) hn] at h

/-- **Item 3.** `dim (Q n ⧸ P n) ≤ rel.card * a (n-2)`, in shifted form `n = k+1`. -/
lemma Qker_le_card_aux (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) (k : ℕ) :
    finrank (ZMod p) ↥(Submodule.map (Submodule.mkQ (Ppow p G α (k + 1)))
        (Qker p G α π (k + 1))) ≤
      rel.card * finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (bG p G ^ k)) := by
  classical
  set T : Submodule (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) :=
    Submodule.map (Submodule.mkQ (Ppow p G α (k + 1))) (Qker p G α π (k + 1)) with hT
  have hrange : ∀ f : rel → MonoidAlgebra (ZMod p) G, psi p G α π rel (k + 1) f ∈ T := by
    intro f
    rw [hT, ← range_psi p G α π rel hπ hrel (k + 1)]
    exact ⟨f, rfl⟩
  let g : (rel → MonoidAlgebra (ZMod p) G) →ₗ[ZMod p] ↥T :=
    (psi p G α π rel (k + 1)).codRestrict T hrange
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [hT, ← range_psi p G α π rel hπ hrel (k + 1)] at hy
    obtain ⟨f, hf⟩ := hy
    exact ⟨f, Subtype.ext hf⟩
  have hker : Submodule.pi Set.univ
      (fun _ : rel => Submodule.restrictScalars (ZMod p) (bG p G ^ k)) ≤ LinearMap.ker g := by
    intro f hf
    rw [LinearMap.mem_ker]
    have h1 : psi p G α π rel (k + 1) f = 0 := by
      have h2 := dRel_pi_le_ker_psi p G α hG π hπ hgen hrel (n := k + 1) (by omega) hf
      rwa [LinearMap.mem_ker] at h2
    apply Subtype.ext
    show (g f : (α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) = 0
    rw [show (g f : (α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) =
        psi p G α π rel (k + 1) f from rfl, h1]
  let G' := Submodule.liftQ (p := Submodule.pi Set.univ
      (fun _ : rel => Submodule.restrictScalars (ZMod p) (bG p G ^ k))) g hker
  have hsurj' : Function.Surjective G' := fun y => by
    obtain ⟨f, hf⟩ := hsurj y
    exact ⟨Submodule.Quotient.mk f, by rw [Submodule.liftQ_apply]; exact hf⟩
  have h1 : finrank (ZMod p) ↥T ≤ finrank (ZMod p)
      ((rel → MonoidAlgebra (ZMod p) G) ⧸ Submodule.pi Set.univ
        (fun _ : rel => Submodule.restrictScalars (ZMod p) (bG p G ^ k))) := by
    have h2 : finrank (ZMod p) ↥T = finrank (ZMod p) ↥(LinearMap.range G') := by
      rw [LinearMap.range_eq_top.mpr hsurj', finrank_top]
    rw [h2]
    exact LinearMap.finrank_range_le G'
  refine le_trans h1 ?_
  rw [finrank_pi_quotient (K := ZMod p) (M := fun _ : rel => MonoidAlgebra (ZMod p) G)
    (fun _ => Submodule.restrictScalars (ZMod p) (bG p G ^ k))]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]

/-- `T = Q n ⧸ P n` inside `(α → B) ⧸ P n`. -/
abbrev Tq (π : FreeGroup α →* G) (k : ℕ) :
    Submodule (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) :=
  Submodule.map (Submodule.mkQ (Ppow p G α (k + 1))) (Qker p G α π (k + 1))

/-- **Item 4, step 1**: the dimension count for `T ⊆ (α → B) ⧸ P n`. -/
lemma finrank_quot_P_add (π : FreeGroup α →* G) (k : ℕ) :
    finrank (ZMod p) (((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) ⧸ Tq p G α π k) +
      finrank (ZMod p) ↥(Tq p G α π k) =
    finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) :=
  Submodule.finrank_quotient_add_finrank _

/-- The quotient of `(α → B) ⧸ P n` by `T` is `(α → B) ⧸ Q n`. -/
lemma finrank_quot_T_eq (π : FreeGroup α →* G) (k : ℕ) :
    finrank (ZMod p) (((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) ⧸ Tq p G α π k) =
      finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Qker p G α π (k + 1)) := by
  refine LinearEquiv.finrank_eq ?_
  exact Submodule.quotientQuotientEquivQuotient (Ppow p G α (k + 1)) (Qker p G α π (k + 1))
    le_sup_right

/-- **The Serre recurrence** (shifted form, `k ≥ 1`). -/
lemma serre_rec_aux (hG : IsPGroup p G) (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) (k : ℕ) :
    Fintype.card α * finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (bG p G ^ (k + 1))) ≤
      rel.card * finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
          Submodule.restrictScalars (ZMod p) (bG p G ^ k)) +
        finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
          Submodule.restrictScalars (ZMod p) (bG p G ^ (k + 2))) - 1 := by
  have h1 := finrank_quot_P_add p G α π k
  have h2 := finrank_quot_T_eq p G α π k
  have h3 := finrank_quot_pi_pow p G α k
  have h4 := finrank_quot_Q p G α π hπ (k + 1)
  have h5 := Qker_le_card_aux p G α hG π hπ hgen hrel k
  have h4' : finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Qker p G α π (k + 1)) =
      finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (bG p G ^ (k + 2))) - 1 := by
    simpa [Ppow, Qker] using h4
  have h3' : finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) =
      Fintype.card α * finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (bG p G ^ (k + 1))) := by
    simpa [Ppow, Qker] using h3
  have h5' : finrank (ZMod p) ↥(Tq p G α π k) ≤ rel.card * finrank (ZMod p)
      (MonoidAlgebra (ZMod p) G ⧸ Submodule.restrictScalars (ZMod p) (bG p G ^ k)) := by
    simpa [Ppow, Qker, Tq] using h5
  have key : finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) =
      finrank (ZMod p) (((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) ⧸ Tq p G α π k) +
        finrank (ZMod p) ↥(Tq p G α π k) := h1.symm
  rw [h3', h2, h4'] at key
  have h1notbG : (1 : MonoidAlgebra (ZMod p) G) ∉ bG p G := by
    rw [bG, RingHom.mem_ker, map_one]
    exact one_ne_zero
  have h1not : (1 : MonoidAlgebra (ZMod p) G) ∉
      Submodule.restrictScalars (ZMod p) (bG p G ^ (k + 2)) := fun h =>
    h1notbG (Ideal.pow_le_self (by omega : k + 2 ≠ 0) h)
  haveI : Nontrivial ((MonoidAlgebra (ZMod p) G) ⧸
      Submodule.restrictScalars (ZMod p) (bG p G ^ (k + 2))) :=
    ⟨⟨Submodule.Quotient.mk (1 : MonoidAlgebra (ZMod p) G), Submodule.Quotient.mk 0, by
      rw [ne_eq, Submodule.Quotient.eq]
      simpa using h1not⟩⟩
  have hge : 1 ≤ finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
      Submodule.restrictScalars (ZMod p) (bG p G ^ (k + 2))) := Module.finrank_pos
  have := h5'
  omega


/-- `A n = dim (B ⧸ bG^n)`; note `A 0 = 0`. -/
abbrev Abar (n : ℕ) : ℕ := finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
  Submodule.restrictScalars (ZMod p) (bG p G ^ n))

/-- The graded dimensions: `b 0 = 1`, `b n = A (n+1) - A n = dim (bG^n / bG^(n+1))`. -/
abbrev bseq (n : ℕ) : ℕ := Abar p G (n + 1) - Abar p G n

lemma Abar_zero : Abar p G 0 = 0 := by
  have h : Submodule.restrictScalars (ZMod p) (bG p G ^ 0) =
      (⊤ : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G)) := by
    rw [Submodule.pow_zero (bG p G), Ideal.one_eq_top,
      Submodule.restrictScalars_top (ZMod p) (MonoidAlgebra (ZMod p) G) (MonoidAlgebra (ZMod p) G)]
  rw [Abar, h]
  have h1 := Submodule.finrank_quotient_add_finrank
    (N := (⊤ : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G))) (M := MonoidAlgebra (ZMod p) G)
  rw [finrank_top] at h1
  omega

lemma Abar_one : Abar p G 1 = 1 := by
  rw [Abar, show bG p G ^ (1 : ℕ) = bG p G from Submodule.pow_one (bG p G)]
  exact finrank_quot_bG p G

lemma bseq_zero : bseq p G 0 = 1 := by
  simp only [bseq, Abar_zero, Abar_one, zero_add, tsub_zero]

/-- `A n ≥ 1` for `n ≥ 1`. -/
lemma Abar_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Abar p G n := by
  have h1notbG : (1 : MonoidAlgebra (ZMod p) G) ∉ bG p G := by
    rw [bG, RingHom.mem_ker, map_one]
    exact one_ne_zero
  have h1not : (1 : MonoidAlgebra (ZMod p) G) ∉
      Submodule.restrictScalars (ZMod p) (bG p G ^ n) :=
    fun h => h1notbG (Ideal.pow_le_self (by omega) h)
  haveI : Nontrivial ((MonoidAlgebra (ZMod p) G) ⧸
      Submodule.restrictScalars (ZMod p) (bG p G ^ n)) :=
    ⟨⟨Submodule.Quotient.mk (1 : MonoidAlgebra (ZMod p) G), Submodule.Quotient.mk 0, by
      rw [ne_eq, Submodule.Quotient.eq]
      simpa using h1not⟩⟩
  exact Module.finrank_pos

/-- `A` is monotone. -/
lemma Abar_mono : Monotone (Abar p G) := by
  intro m n hmn
  have hst : Submodule.restrictScalars (ZMod p) (bG p G ^ n) ≤
      Submodule.restrictScalars (ZMod p) (bG p G ^ m) := Ideal.pow_le_pow_right hmn
  have h1 := Submodule.finrank_quotient_add_finrank
    (N := Submodule.restrictScalars (ZMod p) (bG p G ^ m)) (M := MonoidAlgebra (ZMod p) G)
  have h2 := Submodule.finrank_quotient_add_finrank
    (N := Submodule.restrictScalars (ZMod p) (bG p G ^ n)) (M := MonoidAlgebra (ZMod p) G)
  have hle : finrank (ZMod p) ↥(Submodule.restrictScalars (ZMod p) (bG p G ^ n)) ≤
      finrank (ZMod p) ↥(Submodule.restrictScalars (ZMod p) (bG p G ^ m)) :=
    Submodule.finrank_mono hst
  simp only [Abar]
  omega

/-- The Serre recurrence in `+1` form: `card α * A(n+1) + 1 ≤ rel.card * A n + A (n+2)`. -/
lemma serre_rec_basic (hG : IsPGroup p G) (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) (n : ℕ) :
    Fintype.card α * Abar p G (n + 1) + 1 ≤ rel.card * Abar p G n + Abar p G (n + 2) := by
  have h' : Fintype.card α * Abar p G (n + 1) ≤
      rel.card * Abar p G n + Abar p G (n + 2) - 1 :=
    serre_rec_aux p G α hG π hπ hgen hrel n
  have hb : 1 ≤ rel.card * Abar p G n + Abar p G (n + 2) :=
    le_trans (Abar_pos p G (n := n + 2) (by omega)) (Nat.le_add_left _ _)
  omega

/-- `A` is eventually constant when the augmentation ideal is nilpotent. -/
lemma Abar_eq_nilp (N : ℕ) (hN : bG p G ^ N = ⊥) {m n : ℕ} (hm : N ≤ m) (hn : N ≤ n) :
    Abar p G m = Abar p G n := by
  have hm' : bG p G ^ m = ⊥ := le_bot_iff.mp (by rw [← hN]; exact Ideal.pow_le_pow_right hm)
  have hn' : bG p G ^ n = ⊥ := le_bot_iff.mp (by rw [← hN]; exact Ideal.pow_le_pow_right hn)
  have h_m : Submodule.restrictScalars (ZMod p) (bG p G ^ m) =
      Submodule.restrictScalars (ZMod p) (⊥ : Ideal (MonoidAlgebra (ZMod p) G)) :=
    congrArg (fun I : Ideal (MonoidAlgebra (ZMod p) G) => Submodule.restrictScalars (ZMod p) I) hm'
  have h_n : Submodule.restrictScalars (ZMod p) (bG p G ^ n) =
      Submodule.restrictScalars (ZMod p) (⊥ : Ideal (MonoidAlgebra (ZMod p) G)) :=
    congrArg (fun I : Ideal (MonoidAlgebra (ZMod p) G) => Submodule.restrictScalars (ZMod p) I) hn'
  simp only [Abar]
  rw [h_m, h_n]

/-- The graded dimensions eventually vanish. -/
lemma bseq_eventually_zero (hG : IsPGroup p G) :
    ∀ᶠ n : ℕ in Filter.atTop, bseq p G n = 0 := by
  obtain ⟨N, hN⟩ := isNilpotent_augIdealG p hG
  have hN' : bG p G ^ N = ⊥ := by
    have h := hN
    rwa [show augIdealG p G = bG p G from rfl] at h
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  simp only [bseq]
  have h1 : Abar p G (n + 1) = Abar p G n :=
    Abar_eq_nilp p G N hN' (by omega) (by omega)
  rw [h1, Nat.sub_self]


open GSGen

variable (p : ℕ) [Fact p.Prime] (α : Type*) [Fintype α] [DecidableEq α]
variable (G : Type*) [Group G] [Fintype G]

/-- The Serre equality: `card α · A(k+1) + 1 = A(k+2) + dim T_k`. -/
lemma serre_equality (hG : IsPGroup p G) (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {rel : Finset (FreeGroup α)}
    (hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker) (k : ℕ) :
    Fintype.card α * Abar p G (k + 1) + 1 =
      Abar p G (k + 2) + finrank (ZMod p) ↥(Tq p G α π k) := by
  have h1 := finrank_quot_P_add p G α π k
  have h2 := finrank_quot_T_eq p G α π k
  have h3 := finrank_quot_pi_pow p G α k
  have h4 := finrank_quot_Q p G α π hπ (k + 1)
  have h3' : finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) =
      Fintype.card α * Abar p G (k + 1) := by
    simpa [Ppow, Abar] using h3
  have h4' : finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Qker p G α π (k + 1)) =
      Abar p G (k + 2) - 1 := by
    simpa [Ppow, Qker, Abar] using h4
  have key : finrank (ZMod p) ((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) =
      finrank (ZMod p) (((α → MonoidAlgebra (ZMod p) G) ⧸ Ppow p G α (k + 1)) ⧸ Tq p G α π k) +
        finrank (ZMod p) ↥(Tq p G α π k) := h1.symm
  rw [h3', h2, h4'] at key
  have hge : 1 ≤ Abar p G (k + 2) := Abar_pos p G (by omega)
  omega

/-- `σ` for the group-theoretic `b`: `gsig b k = A(k+1)`. -/
lemma gsig_b_eq (b : ℕ → ℕ) (hb : ∀ j, b j = Abar p G (j+1) - Abar p G j) :
    ∀ k, gsig b k = Abar p G (k+1) := by
  intro k
  induction k with
  | zero =>
      rw [gsig_zero, hb 0, Abar_zero, Abar_one, tsub_zero]
  | succ k ih =>
      rw [gsig_succ, ih, hb (k+1)]
      exact Nat.add_sub_cancel' (Abar_mono p G (by omega : k+1 ≤ k+1+1))

end ScratchSerre

open GSGen ScratchSerre

set_option linter.unusedVariables false in
theorem golod_shafarevich_presentation_card_lt
    (p : ℕ) [Fact p.Prime]
    {α G : Type*} [Fintype α] [DecidableEq α] [Group G] [Fintype G]
    (hG : IsPGroup p G) [Nontrivial G]
    (rel : Finset (FreeGroup α))
    (hpres : Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))))
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) :
    Fintype.card α * Fintype.card α < 4 * rel.card := by
  classical
  let R : Subgroup (FreeGroup α) := Subgroup.normalClosure (rel : Set (FreeGroup α))
  obtain ⟨e⟩ := hpres
  let π : FreeGroup α →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' R)
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨q, rfl⟩ := e.symm.surjective g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    exact ⟨x, rfl⟩
  have hrel : Subgroup.normalClosure (rel : Set (FreeGroup α)) = π.ker := by
    dsimp [π, R]
    ext x
    constructor
    · intro hx
      change x ∈ (e.symm.toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α))))).ker
      rw [MonoidHom.mem_ker]
      have hx' : QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α))) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      simp [MonoidHom.comp_apply, hx']
    · intro hx
      change x ∈ Subgroup.normalClosure (rel : Set (FreeGroup α))
      have hx' : (e.symm.toMonoidHom.comp
          (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α))))) x = 1 := by
        simpa [MonoidHom.mem_ker] using hx
      have hq : QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α))) x = 1 :=
        e.symm.injective (by simpa using hx')
      exact (QuotientGroup.eq_one_iff x).mp hq
  have hcpos : 0 < Fintype.card α := by
    rw [Fintype.card_pos_iff]
    by_contra hnot
    haveI : IsEmpty α := not_nonempty_iff.mp hnot
    haveI : Subsingleton (FreeGroup α) := inferInstance
    have hsub : Subsingleton G := hπ.subsingleton
    exact (not_nontrivial_iff_subsingleton (α := G)).mpr hsub inferInstance
  -- ### algebra data
  let b : ℕ → ℕ := fun j => Abar p G (j+1) - Abar p G j
  let t : ℕ → ℕ := fun k => finrank (ZMod p) ↥(Tq p G α π k)
  obtain ⟨M, hM⟩ := isNilpotent_augIdealG p hG
  have hMb : bG p G ^ M = ⊥ := by
    have h := hM
    rwa [show augIdealG p G = bG p G from rfl] at h
  have hbdef : ∀ j, b j = Abar p G (j+1) - Abar p G j := fun j => rfl
  have hsig : ∀ k, gsig b k = Abar p G (k+1) := gsig_b_eq p G b hbdef
  have hbzero : ∀ j, M ≤ j → b j = 0 := by
    intro j hj
    have h1 : Abar p G (j+1) = Abar p G j := Abar_eq_nilp p G M hMb (by omega) (by omega)
    simp [b, h1]
  have hAbar0 : finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
      Submodule.restrictScalars (ZMod p) (bG p G ^ 0)) = 0 := Abar_zero p G
  have ht0 : t 0 = 0 := by
    have h1 := Qker_le_card_aux p G α hG π hπ hgen hrel 0
    rw [hAbar0, mul_zero] at h1
    exact Nat.eq_zero_of_le_zero h1
  have ht : ∀ k, t (k+1) ≤ rel.card * gsig b k := by
    intro k
    have h1 := Qker_le_card_aux p G α hG π hπ hgen hrel (k+1)
    have h2 : finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (bG p G ^ (k+1))) = gsig b k := (hsig k).symm
    rwa [h2] at h1
  have hrec : ∀ k, Fintype.card α * gsig b k + 1 = gsig b (k+1) + t k := by
    intro k
    have h1 := serre_equality (p := p) (G := G) (α := α) hG π hπ hgen hrel k
    rw [hsig k, hsig (k+1)]
    exact h1
  have hq : ∀ x : ℝ, 0 < x → x < 1 →
      0 < 1 - (Fintype.card α : ℝ)*x + (rel.card : ℝ)*x^2 := by
    intro x hx0 hx1
    have hb := gs_gen_bound (Fintype.card α) rel.card M (M+2) b t (by omega) hbzero ht0 ht hrec x hx0 hx1
    have hBpnn : 0 ≤ (∑ j ∈ Finset.range M, (b j : ℝ) * x^j) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    by_contra hcon
    have hcon' : (1 - (Fintype.card α : ℝ)*x + (rel.card : ℝ)*x^2) ≤ 0 := not_lt.mp hcon
    have := mul_nonpos_of_nonneg_of_nonpos hBpnn hcon'
    linarith
  -- ### Euler characteristic: card α ≤ rel.card
  set D : ℕ := finrank (ZMod p) (MonoidAlgebra (ZMod p) G) with hD
  have hquot : finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
      Submodule.restrictScalars (ZMod p) (bG p G)) = 1 := finrank_quot_bG p G
  have hbridge : finrank (ZMod p) ↥(Submodule.restrictScalars (ZMod p) (bG p G)) =
      finrank (ZMod p) ↥(bG p G) := rfl
  have hbGfin : finrank (ZMod p) ↥(bG p G) = D - 1 := by
    have h1 := Submodule.finrank_quotient_add_finrank
      (N := Submodule.restrictScalars (ZMod p) (bG p G)) (M := MonoidAlgebra (ZMod p) G)
    rw [hquot, ← hD, hbridge] at h1
    omega
  have hpi : finrank (ZMod p) (α → MonoidAlgebra (ZMod p) G) = Fintype.card α * D := by
    rw [finrank_pi_fintype (ZMod p), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hrange : finrank (ZMod p) ↥(LinearMap.range (dRel p α G rel π)) ≤ rel.card * D := by
    have h1 := LinearMap.finrank_range_le (dRel p α G rel π)
    rw [finrank_pi_fintype (ZMod p), Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      smul_eq_mul] at h1
    exact h1
  have hrn := LinearMap.finrank_range_add_finrank_ker (Phi p G α π)
  rw [Phi_range_eq_top p G α π hπ, finrank_top] at hrn
  rw [ker_Phi_eq_range_dRel p G α rel π hπ hrel] at hrn
  have hineq : Fintype.card α * D ≤ rel.card * D + (D - 1) := by
    rw [hbGfin, hpi] at hrn
    omega
  have hD1 : 1 ≤ D := by
    have h1 := Submodule.finrank_quotient_le (R := ZMod p)
      (M := MonoidAlgebra (ZMod p) G) (Submodule.restrictScalars (ZMod p) (bG p G))
    rw [hquot] at h1
    omega
  have hcr : Fintype.card α ≤ rel.card := by
    by_contra hc
    have hle : rel.card + 1 ≤ Fintype.card α := by omega
    have h1 := Nat.mul_le_mul_right D hle
    have h2 : (rel.card + 1) * D = rel.card * D + D := by ring
    omega
  exact quad_final _ _ hcpos hcr hq

