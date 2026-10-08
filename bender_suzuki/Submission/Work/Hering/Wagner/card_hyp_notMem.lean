import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Counting the hyperplanes over `𝔽₂` that avoid a fixed nonzero vector

For a finite `𝔽₂`-vector space `V` of dimension `n` and a nonzero vector `a`, the number of
hyperplanes (codimension-one subspaces) `H` of `V` with `a ∉ H` is `2 ^ (n - 1)`.

The proof identifies hyperplanes with nonzero linear functionals.  Over `𝔽₂` the only nonzero
scalar is `1`, so two nonzero functionals with the same kernel are equal, and every
codimension-one subspace is the kernel of a (unique) nonzero `φ : V →ₗ[𝔽₂] 𝔽₂`
(`Submodule.exists_dual_map_eq_bot_of_notMem` together with the rank formula for `ker`).
Moreover `a ∈ ker φ ↔ φ a = 0`.

Hence the hyperplanes with `a ∉ H` are exactly the kernels of the functionals `φ` with `φ a ≠ 0`,
i.e. `φ a = 1`.  The functionals with `φ a = 1` form a coset of the kernel `K` of the evaluation
map `ev_a : φ ↦ φ a`, which is a hyperplane of the dual `V*` (it is nonzero because `a ≠ 0` can
be extended to a functional with value `1`).  Therefore its cardinality is
`|K| = 2 ^ (finrank V* - 1) = 2 ^ (n - 1)`.
-/

open Module Submodule

namespace Work.Hering.Wagner

/-- In `𝔽₂` the only nonzero element is `1`. -/
private lemma zmod2_ne_zero_eq_one {c : ZMod 2} (h : c ≠ 0) : c = 1 :=
  (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c h

/-- `1 ≠ 0` in `𝔽₂`. -/
private lemma zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- A nonzero vector spans a nontrivial space, so the dimension is at least `1`. -/
private lemma finrank_pos_of_ne_zero (a : V) (ha : a ≠ 0) : 1 ≤ finrank (ZMod 2) V := by
  have hnt : Nontrivial V := ⟨0, a, fun h => ha h.symm⟩
  have h := (Module.finrank_pos_iff (R := ZMod 2) (M := V)).mpr hnt
  omega

/-- A linear functional with `f a = 1` is nonzero. -/
private lemma ne_zero_of_apply_eq_one {f : Module.Dual (ZMod 2) V} {a : V} (h : f a = 1) :
    f ≠ 0 := by
  intro hf
  rw [hf, LinearMap.zero_apply] at h
  exact zmod2_one_ne_zero h.symm

/-- The kernel of a nonzero functional `V →ₗ 𝔽₂` is a hyperplane. -/
private lemma ker_finrank_eq {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) :
    finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) V - 1 := by
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hex : ∃ v, f v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hf (LinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  have hnt : Nontrivial V := ⟨0, v, fun h => hv (by rw [← h]; simp)⟩
  have hpos := (Module.finrank_pos_iff (R := ZMod 2) (M := V)).mpr hnt
  omega

/-- Every hyperplane `H` of `V` with `a ∉ H` is the kernel of a functional taking the value `1`
at `a`. -/
private lemma exists_dual_ker_eq_of_notMem (H : Submodule (ZMod 2) V)
    (hfin : finrank (ZMod 2) H = finrank (ZMod 2) V - 1) {a : V} (ha : a ∉ H) :
    ∃ f : Module.Dual (ZMod 2) V, LinearMap.ker f = H ∧ f a = 1 := by
  obtain ⟨f, hfa, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := H) (x := a) ha inferInstance
  have hfa1 : f a = 1 := zmod2_ne_zero_eq_one hfa
  have hkerfin : finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) V - 1 :=
    ker_finrank_eq (ne_zero_of_apply_eq_one hfa1)
  have hle : H ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hxm : f x ∈ H.map f := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap] at hxm
    simpa using hxm
  exact ⟨f, (Submodule.eq_of_le_of_finrank_eq hle (by rw [hkerfin, hfin])).symm, hfa1⟩

/-- Over `𝔽₂`, the hyperplanes of `V` avoiding `a` correspond to the linear functionals
`f : V →ₗ 𝔽₂` with `f a = 1`, the map being `f ↦ ker f`. -/
private noncomputable def equivDualHyp (a : V) (_ha : a ≠ 0) :
    {f : Module.Dual (ZMod 2) V // f a = 1} ≃
    {H : Submodule (ZMod 2) V // finrank (ZMod 2) H = finrank (ZMod 2) V - 1 ∧ a ∉ H} :=
  Equiv.ofBijective
    (fun f => ⟨LinearMap.ker f.1,
      ker_finrank_eq (ne_zero_of_apply_eq_one f.2),
      by
        intro h
        rw [LinearMap.mem_ker] at h
        rw [f.2] at h
        exact zmod2_one_ne_zero h⟩)
    ⟨fun f g hfg => by
      have hker : LinearMap.ker f.1 = LinearMap.ker g.1 := congrArg Subtype.val hfg
      refine Subtype.ext (Module.Dual.eq_of_ker_eq_of_apply_eq (f := f.1) (g := g.1) a hker ?_ ?_)
      · rw [f.2, g.2]
      · rw [f.2]; exact zmod2_one_ne_zero,
     fun H => by
      obtain ⟨hHfin, hHmem⟩ := H.2
      obtain ⟨f, hfker, hfa⟩ := exists_dual_ker_eq_of_notMem H.1 hHfin hHmem
      exact ⟨⟨f, hfa⟩, Subtype.ext hfker⟩⟩

/-- The functionals `f` with `f a = 1` number `2 ^ (finrank V - 1)`. -/
private lemma dual_fiber_card (a : V) (ha : a ≠ 0) :
    Nat.card {f : Module.Dual (ZMod 2) V // f a = 1}
      = 2 ^ (finrank (ZMod 2) V - 1) := by
  obtain ⟨f₀, hf₀⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) ha
  -- Translation by `f₀` identifies the fibre over `1` with the kernel of the evaluation at `a`.
  have hbij : Nat.card {f : Module.Dual (ZMod 2) V // f a = 1}
      = Nat.card ↥(LinearMap.ker (Module.Dual.eval (ZMod 2) V a)) := by
    refine Nat.card_congr ?_
    refine ⟨fun f => ⟨f.1 - f₀, ?_⟩, fun g => ⟨g.1 + f₀, ?_⟩, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Module.Dual.eval_apply, LinearMap.sub_apply, f.2, hf₀, sub_self]
    · rw [LinearMap.add_apply, (by
        have h := g.2
        rw [LinearMap.mem_ker, Module.Dual.eval_apply] at h
        exact h : g.1 a = 0), zero_add, hf₀]
    · intro f; exact Subtype.ext (sub_add_cancel _ _)
    · intro g; exact Subtype.ext (add_sub_cancel_right _ _)
  rw [hbij]
  -- The kernel of the evaluation map is a subspace of the dual of dimension `finrank V - 1`.
  have hcard : Nat.card ↥(LinearMap.ker (Module.Dual.eval (ZMod 2) V a))
      = 2 ^ finrank (ZMod 2) ↥(LinearMap.ker (Module.Dual.eval (ZMod 2) V a)) := by
    have hint := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(LinearMap.ker (Module.Dual.eval (ZMod 2) V a)))
    rw [Nat.card_zmod] at hint
    exact hint
  rw [hcard]
  congr 1
  have hne : Module.Dual.eval (ZMod 2) V a ≠ 0 := by
    intro h
    have h1 : (Module.Dual.eval (ZMod 2) V a) f₀ = 0 := by rw [h]; simp
    rw [Module.Dual.eval_apply] at h1
    rw [h1] at hf₀
    exact zmod2_one_ne_zero hf₀.symm
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [Subspace.dual_finrank_eq] at h1
  have hpos := finrank_pos_of_ne_zero a ha
  omega

end

theorem card_hyp_notMem {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (a : V) (ha : a ≠ 0) :
    Nat.card {H : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) H = Module.finrank (ZMod 2) V - 1 ∧ a ∉ H}
      = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  rw [← Nat.card_congr (equivDualHyp a ha)]
  exact dual_fiber_card a ha

end Work.Hering.Wagner
