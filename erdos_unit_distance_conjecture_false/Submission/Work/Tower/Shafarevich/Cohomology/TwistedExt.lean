import Mathlib

/-!
# Twisted (central) extensions of a group by `𝔽_p`

Given a **normalized `2`-cocycle** `c` on a group `G` with values in `𝔽_p` (trivial action),
the twisted product `(a, g) * (b, h) = (a + b + c (g, h), g * h)` makes `𝔽_p × G` a group,
the central extension of `G` by `𝔽_p` classified by `c`.  This file builds that group and the
associated function `ExtGroup.tau`, the first coordinate of the lift of a homomorphism
`φ : FreeGroup (Fin d) →* G` to the extension.  It is the `τ`-function characterising `c`:
`τ 1 = 0`, `τ (x_i) = 0` and `τ (u * v) = τ u + τ v + c (φ u, φ v)`.

These are the objects in which the proof of `dim H²(G, 𝔽_p) ≤ r(G)` is phrased.
-/

namespace Work.Tower.Shafarevich.Cohomology

open scoped Classical

/-- A **normalized `2`-cocycle** on a group `G` with values in `ZMod p` for the trivial action of
`G`, written additively: a function `c : G × G → ZMod p` with
`c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j)` and `c (1, 1) = 0`. -/
structure TwistedCocycle (p : ℕ) (G : Type*) [Group G] where
  toFun : G × G → ZMod p
  cocycle : ∀ g h j : G, toFun (g * h, j) + toFun (g, h) = toFun (h, j) + toFun (g, h * j)
  map_one_one : toFun (1, 1) = 0

namespace TwistedCocycle

variable {p : ℕ} {G : Type*} [Group G]

instance : CoeFun (TwistedCocycle p G) (fun _ => G × G → ZMod p) := ⟨TwistedCocycle.toFun⟩

@[simp] theorem toFun_eq (c : TwistedCocycle p G) : c.toFun = ⇑c := rfl

@[ext] theorem ext {c c' : TwistedCocycle p G} (h : ∀ x, c x = c' x) : c = c' := by
  obtain ⟨f, hf, h1⟩ := c
  obtain ⟨f', hf', h1'⟩ := c'
  have hff : f = f' := funext h
  subst hff
  congr

/-- `c (1, g) = 0` for a normalized cocycle. -/
theorem map_one_fst (c : TwistedCocycle p G) (g : G) : c (1, g) = 0 := by
  have h := c.cocycle 1 1 g
  simp only [one_mul, c.map_one_one, add_zero] at h
  have h2 : c (1, g) + 0 = c (1, g) + c (1, g) := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- `c (g, 1) = 0` for a normalized cocycle. -/
theorem map_one_snd (c : TwistedCocycle p G) (g : G) : c (g, 1) = 0 := by
  have h := c.cocycle g 1 1
  simp only [mul_one, c.map_one_one, zero_add] at h
  have h2 : c (g, 1) + c (g, 1) = c (g, 1) + 0 := by rw [add_zero]; exact h
  exact add_left_cancel h2

/-- `c (g, g⁻¹) = c (g⁻¹, g)`: the two "inverse" values of a normalized cocycle agree. -/
theorem map_inv_eq (c : TwistedCocycle p G) (g : G) : c (g, g⁻¹) = c (g⁻¹, g) := by
  have h := c.cocycle g g⁻¹ g
  simpa [mul_inv_cancel, inv_mul_cancel, c.map_one_fst, c.map_one_snd] using h

instance : Add (TwistedCocycle p G) where
  add c c' :=
    { toFun := c.toFun + c'.toFun
      cocycle := by
        intro g h j
        have hc := c.cocycle g h j
        have hc' := c'.cocycle g h j
        simp only [Pi.add_apply]
        linear_combination hc + hc'
      map_one_one := by
        simp only [Pi.add_apply, c.map_one_one, c'.map_one_one, add_zero] }

instance : Zero (TwistedCocycle p G) where
  zero := { toFun := 0, cocycle := by intro g h j; simp, map_one_one := rfl }

instance : SMul (ZMod p) (TwistedCocycle p G) where
  smul s c :=
    { toFun := s • c.toFun
      cocycle := by
        intro g h j
        simp only [Pi.smul_apply, ← smul_add, c.cocycle g h j]
      map_one_one := by simp [c.map_one_one] }

@[simp] theorem add_apply (c c' : TwistedCocycle p G) (x : G × G) :
    (c + c') x = c x + c' x := rfl

@[simp] theorem zero_apply (x : G × G) : (0 : TwistedCocycle p G) x = 0 := rfl

@[simp] theorem smul_apply (s : ZMod p) (c : TwistedCocycle p G) (x : G × G) :
    (s • c) x = s • c x := rfl

end TwistedCocycle

/-- The central extension of `G` by `ZMod p` determined by a normalized `2`-cocycle `c`: the
type `ZMod p × G` with the twisted group law `(a, g) * (b, h) = (a + b + c (g, h), g * h)`. -/
structure ExtGroup {p : ℕ} (G : Type*) [Group G] (c : TwistedCocycle p G) where
  /-- the `ZMod p`-coordinate -/
  a : ZMod p
  /-- the `G`-coordinate -/
  g : G

namespace ExtGroup

variable {p : ℕ} {G : Type*} [Group G] {c : TwistedCocycle p G}

instance : Mul (ExtGroup G c) :=
  ⟨fun x y => ⟨x.a + y.a + c (x.g, y.g), x.g * y.g⟩⟩

instance : One (ExtGroup G c) := ⟨⟨0, 1⟩⟩

instance : Inv (ExtGroup G c) := ⟨fun x => ⟨-x.a - c (x.g, x.g⁻¹), x.g⁻¹⟩⟩

@[simp] theorem mul_a (x y : ExtGroup G c) : (x * y).a = x.a + y.a + c (x.g, y.g) := rfl
@[simp] theorem mul_g (x y : ExtGroup G c) : (x * y).g = x.g * y.g := rfl
@[simp] theorem one_a : (1 : ExtGroup G c).a = 0 := rfl
@[simp] theorem one_g : (1 : ExtGroup G c).g = 1 := rfl
@[simp] theorem inv_a (x : ExtGroup G c) : x⁻¹.a = -x.a - c (x.g, x.g⁻¹) := rfl
@[simp] theorem inv_g (x : ExtGroup G c) : x⁻¹.g = x.g⁻¹ := rfl

theorem ext {x y : ExtGroup G c} (ha : x.a = y.a) (hg : x.g = y.g) : x = y := by
  cases x; cases y; simp_all

theorem one_mul (x : ExtGroup G c) : 1 * x = x := by
  refine ext ?_ ?_ <;> simp [TwistedCocycle.map_one_fst]

theorem mul_one (x : ExtGroup G c) : x * 1 = x := by
  refine ext ?_ ?_ <;> simp [TwistedCocycle.map_one_snd]

theorem mul_assoc (x y z : ExtGroup G c) : x * y * z = x * (y * z) := by
  have hc := c.cocycle x.g y.g z.g
  refine ext ?_ ?_ <;> simp only [mul_a, mul_g]
  · linear_combination hc
  · rw [_root_.mul_assoc]

theorem inv_mul_cancel (x : ExtGroup G c) : x⁻¹ * x = 1 := by
  refine ext ?_ ?_ <;> simp only [mul_a, inv_a, inv_g, one_a, one_g]
  · rw [TwistedCocycle.map_inv_eq]; ring
  · simp

/-- The group structure on the twisted extension `ZMod p × G`. -/
instance instGroup : Group (ExtGroup G c) :=
  Group.ofLeftAxioms mul_assoc one_mul inv_mul_cancel

/-- The second projection `ExtGroup G c →* G`. -/
def sndHom : ExtGroup G c →* G where
  toFun x := x.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem sndHom_apply (x : ExtGroup G c) : sndHom x = x.g := rfl

/-- The lift of `φ` to the twisted extension, sending the free generator `x_i` to
`(0, φ x_i)`. -/
def lift (c : TwistedCocycle p G) {d : ℕ} (φ : FreeGroup (Fin d) →* G) :
    FreeGroup (Fin d) →* ExtGroup G c :=
  FreeGroup.lift fun i => ⟨0, φ (FreeGroup.of i)⟩

theorem snd_lift (c : TwistedCocycle p G) {d : ℕ} (φ : FreeGroup (Fin d) →* G)
    (w : FreeGroup (Fin d)) : (lift c φ w).g = φ w := by
  have h := FreeGroup.lift_unique (g := (sndHom (c := c)).comp (lift c φ))
      (f := fun i => φ (FreeGroup.of i)) (fun i => by simp [lift]) (x := w)
  have h2 := FreeGroup.lift_unique (g := φ) (f := fun i => φ (FreeGroup.of i))
      (fun i => rfl) (x := w)
  simpa using h.trans h2.symm

/-- The `τ` of a normalized `2`-cocycle `c` relative to `φ`: the first coordinate of the lift
of `φ` to the twisted extension `ExtGroup G c`.  It satisfies `τ 1 = 0`, `τ (x_i) = 0` and
`τ (u * v) = τ u + τ v + c (φ u, φ v)`. -/
def tau (c : TwistedCocycle p G) {d : ℕ} (φ : FreeGroup (Fin d) →* G) :
    FreeGroup (Fin d) → ZMod p :=
  fun w => (lift c φ w).a

theorem tau_one (c : TwistedCocycle p G) {d : ℕ} (φ : FreeGroup (Fin d) →* G) :
    tau c φ 1 = 0 := by
  simp [tau]

theorem tau_of (c : TwistedCocycle p G) {d : ℕ} (φ : FreeGroup (Fin d) →* G) (i : Fin d) :
    tau c φ (FreeGroup.of i) = 0 := by
  simp [tau, lift]

theorem tau_mul (c : TwistedCocycle p G) {d : ℕ} (φ : FreeGroup (Fin d) →* G)
    (u v : FreeGroup (Fin d)) :
    tau c φ (u * v) = tau c φ u + tau c φ v + c (φ u, φ v) := by
  simp only [tau, map_mul, mul_a, snd_lift]

end ExtGroup

end Work.Tower.Shafarevich.Cohomology
