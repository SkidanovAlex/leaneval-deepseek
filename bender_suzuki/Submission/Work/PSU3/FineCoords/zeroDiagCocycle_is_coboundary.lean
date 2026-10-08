import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PSU3.FineCoords

/-!
# Normalized `2`-cocycles with vanishing diagonal on an elementary abelian `2`-group

Let `V` be a finite `𝔽₂`-module and `M` an abelian group of exponent `2` (a commutative group
with `x * x = 1`).  Suppose `c : V → V → M` is a normalized `2`-cocycle,

  `c 0 v = 1`,  `c v 0 = 1`,  `c v u * c (v + u) w = c u w * c v (u + w)`,

whose diagonal vanishes, `c v v = 1`.  Then `c` is a **coboundary**: there is `f : V → M`
with `f 0 = 1` and `c v u = f (v + u) * f v * f u`.

The mathematical content is that `c` defines a central extension `E` of `V` by `M`; the
cocycle identity makes the multiplication on `E` associative, and vanishing diagonal makes
`E` have exponent `2`, while the hypotheses force `c` to be symmetric, i.e. `E` abelian.
Hence `E` is an `𝔽₂`-vector space and the projection `E → V` admits a linear section, whose
second coordinate is `f`.

We build `E` explicitly as the (twisted) additive group `CocycleExt V M` and obtain the
section from `LinearMap.exists_rightInverse_of_surjective`.
-/

/-- The underlying type of the central extension attached to a cochain `c : V → V → M`:
pairs `(v, m)`.  Its additive structure (installed locally inside the proof of
`zeroDiagCocycle_is_coboundary`) is the twisted one
`(v, a) + (u, b) = (v + u, a + b + c v u)`. -/
structure CocycleExt (V : Type*) (M : Type*) where
  /-- The `V`-coordinate. -/
  fst : V
  /-- The `M`-coordinate. -/
  snd : M

@[ext]
theorem CocycleExt.ext {V M : Type*} {p q : CocycleExt V M}
    (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  cases p; cases q; simp_all

/-- A rearrangement in any commutative group: `a * b * g * a * b = g * (a * a) * (b * b)`. -/
private lemma cg_rearr {G : Type*} [CommGroup G] (a b g : G) :
    a * b * g * a * b = g * (a * a) * (b * b) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul]
  abel

theorem zeroDiagCocycle_is_coboundary
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {M : Type*} [CommGroup M] (hM : ∀ x : M, x * x = 1)
    (c : V → V → M)
    (h0l : ∀ v, c 0 v = 1) (h0r : ∀ v, c v 0 = 1)
    (hcoc : ∀ v u w, c v u * c (v + u) w = c u w * c v (u + w))
    (hdiag : ∀ v, c v v = 1) :
    ∃ f : V → M, f 0 = 1 ∧ ∀ v u, c v u = f (v + u) * f v * f u := by
  classical
  -- Work multiplicatively on `M`, but additively on `M` through `Additive M`, so that the
  -- group-theoretic rearrangements become `abel`-able.
  let cad : V → V → Additive M := fun v u => Additive.ofMul (c v u)
  have h0l' : ∀ v, cad 0 v = 0 := by intro v; simp [cad, h0l v]
  have h0r' : ∀ v, cad v 0 = 0 := by intro v; simp [cad, h0r v]
  have hdiag' : ∀ v, cad v v = 0 := by intro v; simp [cad, hdiag v]
  have hcoc' : ∀ v u w, cad v u + cad (v + u) w = cad u w + cad v (u + w) := by
    intro v u w; simp only [cad, ← ofMul_mul, hcoc v u w]
  have hM' : ∀ x : Additive M, x + x = 0 := by
    intro x; rw [← ofMul_toMul x, ← ofMul_mul, hM, ofMul_one]
  -- `c` is symmetric.  Indeed the cocycle identity with `u = v` (and `v + v = 0`) gives
  -- `c x (x + y) = c x y * c x x`; feeding this into the cocycle identity at `(v, u, v + u)`
  -- shows `c v u * c u v = 1`, hence `c v u = c u v`.
  have hsymm' : ∀ v u, cad v u = cad u v := by
    intro v u
    have hstep : ∀ x y : V, cad x (x + y) = cad x y + cad x x := by
      intro x y
      have h := hcoc' x x y
      rw [ZModModule.add_self, h0l' y, add_zero] at h
      rw [h, ← add_assoc, hM' (cad x y), zero_add]
    have h1 := hcoc' v u (v + u)
    have hu : u + (v + u) = v := by
      rw [add_comm v u, ← add_assoc, ZModModule.add_self, zero_add]
    rw [hdiag' (v + u), add_zero, hu, hdiag' v, add_zero] at h1
    have h2 := hstep u v
    rw [show u + v = v + u by abel, hdiag' u, add_zero] at h2
    exact h1.trans h2
  -- Build the central extension `E` with the twisted addition `(v, a) + (u, b) = (v+u, a+b+c v u)`.
  let addE : CocycleExt V (Additive M) → CocycleExt V (Additive M) → CocycleExt V (Additive M) :=
    fun p q => ⟨p.fst + q.fst, p.snd + q.snd + cad p.fst q.fst⟩
  letI : Zero (CocycleExt V (Additive M)) := ⟨⟨(0 : V), (0 : Additive M)⟩⟩
  letI : Add (CocycleExt V (Additive M)) := ⟨addE⟩
  letI : Neg (CocycleExt V (Additive M)) := ⟨fun p => p⟩
  have hfst : ∀ p q : CocycleExt V (Additive M), (p + q).fst = p.fst + q.fst := fun _ _ => rfl
  letI : AddCommGroup (CocycleExt V (Additive M)) :=
    { add := addE
      zero := 0
      neg := fun p => p
      sub := fun p q => addE p q
      nsmul := nsmulRec
      zsmul := zsmulRec
      add_assoc := by
        rintro ⟨v, a⟩ ⟨u, b⟩ ⟨w, d⟩
        refine CocycleExt.ext ?_ ?_
        · show v + u + w = v + (u + w); abel
        · show (a + b + cad v u) + d + cad (v + u) w = a + (b + d + cad u w) + cad v (u + w)
          rw [show (a + b + cad v u) + d + cad (v + u) w
                = a + b + (cad v u + cad (v + u) w) + d by abel,
              hcoc' v u w,
              show a + b + (cad u w + cad v (u + w)) + d
                = a + (b + d + cad u w) + cad v (u + w) by abel]
      zero_add := by
        rintro ⟨v, a⟩
        refine CocycleExt.ext ?_ ?_
        · show (0 : V) + v = v; abel
        · show (0 : Additive M) + a + cad 0 v = a; rw [h0l' v, add_zero, zero_add]
      add_zero := by
        rintro ⟨v, a⟩
        refine CocycleExt.ext ?_ ?_
        · show v + 0 = v; abel
        · show a + 0 + cad v 0 = a; rw [h0r' v, add_zero, add_zero]
      neg_add_cancel := by
        rintro ⟨v, a⟩
        refine CocycleExt.ext ?_ ?_
        · show v + v = 0; exact ZModModule.add_self v
        · show a + a + cad v v = 0; rw [hM' a, hdiag' v, add_zero]
      add_comm := by
        rintro ⟨v, a⟩ ⟨u, b⟩
        refine CocycleExt.ext ?_ ?_
        · show v + u = u + v; abel
        · show a + b + cad v u = b + a + cad u v; rw [hsymm' v u]; abel }
  -- `E` has exponent `2`, so it is an `𝔽₂`-vector space.
  letI : Module (ZMod 2) (CocycleExt V (Additive M)) :=
    AddCommGroup.zmodModule (fun x => by rw [two_nsmul]; exact neg_add_cancel x)
  have hfst_nsmul : ∀ (n : ℕ) (p : CocycleExt V (Additive M)), (n • p).fst = n • p.fst := by
    intro n
    induction n with
    | zero => intro p; rw [zero_nsmul, zero_nsmul]; rfl
    | succ n ih => intro p; rw [AddMonoid.nsmul_succ, AddMonoid.nsmul_succ, hfst, ih]
  -- The projection `E → V` is linear and surjective, hence has a linear section.
  let π : CocycleExt V (Additive M) →ₗ[ZMod 2] V :=
    { toFun := fun p => p.fst
      map_add' := fun _ _ => rfl
      map_smul' := fun r p => by
        show (r.val • p).fst = r • p.fst
        rw [hfst_nsmul r.val p, ← Nat.cast_smul_eq_nsmul (ZMod 2) r.val p.fst, ZMod.natCast_zmod_val] }
  have hsurj : Function.Surjective π := fun v => ⟨⟨v, 0⟩, rfl⟩
  obtain ⟨s, hs⟩ :=
    LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.2 hsurj)
  have hsv : ∀ v, (s v).fst = v := fun v => by
    have := LinearMap.ext_iff.1 hs v
    simpa [π] using this
  -- The second coordinate of the section is the desired coboundary.
  refine ⟨fun v => (s v).snd.toMul, ?_, ?_⟩
  · show (s 0).snd.toMul = 1
    rw [map_zero]; rfl
  · intro v u
    show c v u = (s (v + u)).snd.toMul * (s v).snd.toMul * (s u).snd.toMul
    have h := s.map_add v u
    have h2 : (s (v + u)).snd = (s v).snd + (s u).snd + cad (s v).fst (s u).fst := by rw [h]; rfl
    have h3 := congrArg Additive.toMul h2
    simp only [toMul_add, hsv, cad, toMul_ofMul] at h3
    rw [h3, cg_rearr, hM, hM, mul_one, mul_one]

end Work.PSU3.FineCoords
