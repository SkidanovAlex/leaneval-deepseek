import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped BigOperators

namespace Commons.GroupTheory.Subgroup

noncomputable section

variable {G : Type*} [Group G]

/-- The double coset `HxH`, as a set of elements of `G`. -/
private def dcos (H : Subgroup G) (x : G) : Set G :=
  {y : G | ∃ a b : H, y = (a : G) * x * (b : G)}

/-- Elements of `H` whose `x`-conjugate is again in `H`, i.e. the intersection `H ∩ xHx⁻¹`
expressed with explicit membership data. -/
private def conjStab (H : Subgroup G) (x : G) : Type _ :=
  {l : G // l ∈ (H : Set G) ∧ x⁻¹ * l * x ∈ (H : Set G)}

/-- The fiber over `y : G` of the map `(a, b) ↦ a * x * b` from `H × H`. -/
private def FiberEq (H : Subgroup G) (x : G) (y : G) : Type _ :=
  {p : H × H // (p.1 : G) * x * (p.2 : G) = y}

/-- `l ∈ H^x` (the image of `H` under conjugation by `x`) iff `x⁻¹lx ∈ H`. -/
private theorem conjStab_mem_map_iff (H : Subgroup G) (x : G) {l : G} :
    l ∈ H.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * l * x ∈ (H : Set G) := by
  constructor
  · intro hl
    rw [Subgroup.mem_map] at hl
    rcases hl with ⟨h, hh, hl⟩
    have hl' : x * h * x⁻¹ = l := by
      simpa [MulAut.conj_apply] using hl
    have : x⁻¹ * l * x = h := by
      calc
        x⁻¹ * l * x = x⁻¹ * (l * x) := by rw [mul_assoc]
        _ = x⁻¹ * ((x * h * x⁻¹) * x) := by rw [hl']
        _ = h := by simp [mul_assoc]
    rw [this]
    exact hh
  · intro hlx
    rw [Subgroup.mem_map]
    refine ⟨x⁻¹ * l * x, hlx, ?_⟩
    change x * (x⁻¹ * l * x) * x⁻¹ = l
    group

/-- `conjStab H x ≃ H ⊓ H^x`. -/
private def conjStab_equiv_inf (H : Subgroup G) (x : G) :
    conjStab H x ≃ (H ⊓ H.map (MulAut.conj x).toMonoidHom : Subgroup G) := by
  refine Equiv.subtypeEquivRight ?_
  intro l
  constructor
  · rintro ⟨hH, hlx⟩
    rw [Subgroup.mem_inf]
    exact ⟨hH, (conjStab_mem_map_iff H x).2 hlx⟩
  · intro hl
    rw [Subgroup.mem_inf] at hl
    exact ⟨hl.1, (conjStab_mem_map_iff H x).1 hl.2⟩

/-- Forget the right factor: `(a, b) ↦ a` from the fiber over `x` to `conjStab H x`. -/
private def FiberEq_x_to (H : Subgroup G) (x : G) : FiberEq H x x → conjStab H x
  | ⟨⟨a, b⟩, hp⟩ => ⟨(a : G), ⟨a.property, by
      have h1 : (a : G) * x = x * (b : G)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : G => t * (b : G)⁻¹) hp
      have : x⁻¹ * (a : G) * x = (b : G)⁻¹ := by
        calc
          x⁻¹ * (a : G) * x = x⁻¹ * ((a : G) * x) := by rw [mul_assoc]
          _ = x⁻¹ * (x * (b : G)⁻¹) := congrArg (fun t : G => x⁻¹ * t) h1
          _ = (b : G)⁻¹ := by simp
      rw [this]
      exact Subgroup.inv_mem H b.property⟩⟩

private theorem FiberEq_x_to_injective (H : Subgroup G) (x : G) :
    Function.Injective (FiberEq_x_to H x) := by
  rintro ⟨⟨a₁, b₁⟩, h₁⟩ ⟨⟨a₂, b₂⟩, h₂⟩ hφ
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    have hv : (a₁ : G) = (a₂ : G) := by
      simpa [FiberEq_x_to] using congrArg Subtype.val hφ
    exact hv
  · apply Subtype.ext
    have hv : (a₁ : G) = (a₂ : G) := by
      simpa [FiberEq_x_to] using congrArg Subtype.val hφ
    have h₁' : (a₁ : G) * x * (b₁ : G) = x := by simpa using h₁
    have h₂v : (a₂ : G) * x * (b₂ : G) = x := by simpa using h₂
    have h₂' : (a₁ : G) * x * (b₂ : G) = x := by
      rw [hv]
      exact h₂v
    have he : (a₁ : G) * x * (b₁ : G) = (a₁ : G) * x * (b₂ : G) := h₁'.trans h₂'.symm
    exact mul_left_cancel he

private theorem FiberEq_x_to_surjective (H : Subgroup G) (x : G) :
    Function.Surjective (FiberEq_x_to H x) := by
  rintro ⟨l, hH, hlx⟩
  let a : H := ⟨l, hH⟩
  let b : H := ⟨(x⁻¹ * l * x)⁻¹, Subgroup.inv_mem H hlx⟩
  have hprod : (a : G) * x * (b : G) = x := by
    dsimp [a, b]
    simp [mul_assoc]
  refine ⟨⟨(a, b), hprod⟩, ?_⟩
  · apply Subtype.ext
    rfl

/-- The fiber over `x` is in bijection with `conjStab H x`. -/
private def FiberEq_x_equiv_conjStab (H : Subgroup G) (x : G) :
    FiberEq H x x ≃ conjStab H x :=
  Equiv.ofBijective (FiberEq_x_to H x) ⟨FiberEq_x_to_injective H x, FiberEq_x_to_surjective H x⟩

/-- Translate `(c, d) ↦ (a₀ * c, d * b₀)`: from the fiber over `x` to the fiber over
`y = a₀ x b₀`. -/
private def FiberEq_x_to_y (H : Subgroup G) (x : G) {y : G} (a₀ b₀ : H)
    (hy : y = (a₀ : G) * x * (b₀ : G)) : FiberEq H x x → FiberEq H x y
  | ⟨⟨c, d⟩, hcd⟩ => ⟨(a₀ * c, d * b₀), by
      calc
        ((a₀ * c : H) : G) * x * ((d * b₀ : H) : G)
            = (a₀ : G) * ((c : G) * x * (d : G)) * (b₀ : G) := by simp [mul_assoc]
        _ = (a₀ : G) * x * (b₀ : G) := by rw [hcd]
        _ = y := hy.symm⟩

private theorem FiberEq_x_to_y_injective (H : Subgroup G) (x : G) {y : G} (a₀ b₀ : H)
    (hy : y = (a₀ : G) * x * (b₀ : G)) : Function.Injective (FiberEq_x_to_y H x a₀ b₀ hy) := by
  rintro ⟨⟨c₁, d₁⟩, h₁⟩ ⟨⟨c₂, d₂⟩, h₂⟩ hφ
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    have hpair : ((a₀ * c₁ : H) : G) = ((a₀ * c₂ : H) : G) := by
      simpa [FiberEq_x_to_y] using congrArg (fun p : H × H => (p.1 : G)) (congrArg Subtype.val hφ)
    simpa [mul_assoc] using mul_left_cancel hpair
  · apply Subtype.ext
    have hpair : ((d₁ * b₀ : H) : G) = ((d₂ * b₀ : H) : G) := by
      simpa [FiberEq_x_to_y] using congrArg (fun p : H × H => (p.2 : G)) (congrArg Subtype.val hφ)
    have hb : (d₁ : G) * (b₀ : G) = (d₂ : G) * (b₀ : G) := by simpa [mul_assoc] using hpair
    exact mul_right_cancel hb

private theorem FiberEq_x_to_y_surjective (H : Subgroup G) (x : G) {y : G} (a₀ b₀ : H)
    (hy : y = (a₀ : G) * x * (b₀ : G)) : Function.Surjective (FiberEq_x_to_y H x a₀ b₀ hy) := by
  rintro ⟨⟨a', b'⟩, hab⟩
  let c : H := a₀⁻¹ * a'
  let d : H := b' * b₀⁻¹
  have hprod : (c : G) * x * (d : G) = x := by
    dsimp [c, d]
    have hab' : (a' : G) * x * (b' : G) = (a₀ : G) * x * (b₀ : G) := by
      simpa [hy] using hab
    change ((a₀ : G)⁻¹ * (a' : G)) * x * ((b' : G) * (b₀ : G)⁻¹) = x
    calc
      ((a₀ : G)⁻¹ * (a' : G)) * x * ((b' : G) * (b₀ : G)⁻¹)
          = (a₀ : G)⁻¹ * ((a' : G) * x * (b' : G)) * (b₀ : G)⁻¹ := by simp [mul_assoc]
      _ = (a₀ : G)⁻¹ * ((a₀ : G) * x * (b₀ : G)) * (b₀ : G)⁻¹ := by rw [hab']
      _ = x := by simp [mul_assoc]
  refine ⟨⟨(c, d), hprod⟩, ?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [FiberEq_x_to_y, c, d, mul_assoc]
    · apply Subtype.ext
      simp [FiberEq_x_to_y, c, d, mul_assoc]

/-- Fibers over two elements of the same double coset are equinumerous. -/
private def FiberEq_translate (H : Subgroup G) (x : G) {y : G} (a₀ b₀ : H)
    (hy : y = (a₀ : G) * x * (b₀ : G)) : FiberEq H x x ≃ FiberEq H x y :=
  Equiv.ofBijective (FiberEq_x_to_y H x a₀ b₀ hy)
    ⟨FiberEq_x_to_y_injective H x a₀ b₀ hy, FiberEq_x_to_y_surjective H x a₀ b₀ hy⟩

/-- The fiber over any element of the double coset has the cardinality of `conjStab H x`. -/
private theorem fiber_card_eq_conjStab (H : Subgroup G) (x : G) :
    ∀ y : {y : G // y ∈ dcos H x},
      Nat.card (FiberEq H x (y : G)) = Nat.card (conjStab H x) := by
  rintro ⟨y, hy⟩
  rcases hy with ⟨a₀, b₀, hy_eq⟩
  calc
    Nat.card (FiberEq H x y) = Nat.card (FiberEq H x x) := by
      exact (Nat.card_congr (FiberEq_translate H x a₀ b₀ hy_eq)).symm
    _ = Nat.card (conjStab H x) := Nat.card_congr (FiberEq_x_equiv_conjStab H x)

/-- The map `(a, b) ↦ a * x * b`, viewed as landing in the double coset subtype. -/
private def dcosMap (H : Subgroup G) (x : G) : H × H → {y : G // y ∈ dcos H x} :=
  fun p => ⟨(p.1 : G) * x * (p.2 : G), ⟨p.1, p.2, rfl⟩⟩

/-- The fiber of `dcosMap` over `y` is the fiber of `(a, b) ↦ a * x * b` over `y`. -/
private def fiberF_equiv_FiberEq (H : Subgroup G) (x : G) (y : {y : G // y ∈ dcos H x}) :
    {p : H × H // dcosMap H x p = y} ≃ FiberEq H x (y : G) := by
  refine Equiv.subtypeEquivRight ?_
  intro p
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- Sum of a constant function over a finite type. -/
private theorem sum_const_natCard {D : Type*} [Fintype D] (c : ℕ) :
    (∑ _ : D, c) = Nat.card D * c := by
  rw [Nat.card_eq_fintype_card]
  simp [Finset.sum_const]

/-- `|H × H| = |HxH| · |H ∩ xHx⁻¹|`, for finite `G`. -/
private theorem dcos_card_eq (H : Subgroup G) (x : G) [Fintype G] :
    Nat.card (H × H) =
      Nat.card {y : G // y ∈ dcos H x} * Nat.card (conjStab H x) := by
  classical
  let D : Type _ := {y : G // y ∈ dcos H x}
  let F : H × H → D := fun p => ⟨(p.1 : G) * x * (p.2 : G), ⟨p.1, p.2, rfl⟩⟩
  calc
    Nat.card (H × H) = Nat.card (Sigma fun y : D => {p : H × H // F p = y}) := by
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv F)).symm
    _ = ∑ y : D, Nat.card {p : H × H // F p = y} := by
      exact Nat.card_sigma
    _ = ∑ y : D, Nat.card (conjStab H x) := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        Nat.card {p : H × H // F p = y} = Nat.card (FiberEq H x (y : G)) := by
          exact Nat.card_congr (fiberF_equiv_FiberEq H x y)
        _ = Nat.card (conjStab H x) := fiber_card_eq_conjStab H x y
    _ = Nat.card D * Nat.card (conjStab H x) := by
      exact sum_const_natCard (D := D) (Nat.card (conjStab H x))

end

/-- The order of a double coset `HxH` times the order of `H ∩ xHx⁻¹` equals `|H|²`. -/
theorem card_doubleCoset_mul {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (x : G) :
    Nat.card {y : G | ∃ a b : H, y = (a : G) * x * (b : G)} *
        Nat.card (H ⊓ H.map (MulAut.conj x).toMonoidHom : Subgroup G) =
      Nat.card H * Nat.card H := by
  classical
  have hD : Nat.card {y : G | ∃ a b : H, y = (a : G) * x * (b : G)} =
      Nat.card {y : G // y ∈ dcos H x} := rfl
  have hL : Nat.card (H ⊓ H.map (MulAut.conj x).toMonoidHom : Subgroup G) =
      Nat.card (conjStab H x) := by
    exact (Nat.card_congr (conjStab_equiv_inf H x)).symm
  calc
    Nat.card {y : G | ∃ a b : H, y = (a : G) * x * (b : G)} *
        Nat.card (H ⊓ H.map (MulAut.conj x).toMonoidHom : Subgroup G)
        = Nat.card {y : G // y ∈ dcos H x} * Nat.card (conjStab H x) := by
          rw [hD, hL]
    _ = Nat.card (H × H) := (dcos_card_eq H x).symm
    _ = Nat.card H * Nat.card H := by rw [Nat.card_prod]

end Commons.GroupTheory.Subgroup