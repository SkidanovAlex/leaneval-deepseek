import Mathlib

-- The problem statement uses the universe level `u`; make it explicit so that the file
-- compiles with `autoImplicit = false` (set in the lakefile).
universe u

set_option linter.style.haveILetI false

namespace Work.WallSystem

/-- Let a group `H` act on the vertex set `X` of a connected, locally finite graph `G` by
graph automorphisms, freely, with finitely many orbits of vertices.  Then `H` is finitely
generated.

The generating set is finite because it only involves the neighbours of one representative
vertex per orbit: for each vertex `x`, `R x` is the (unique) group element carrying `x` to the
chosen representative of its orbit, and the generators are the elements `R u` with `u` a
neighbour of a chosen representative. -/
theorem fg_of_free_cocompact_graph {H : Type u} [Group H] {X : Type u} [MulAction H X]
    [Nonempty X] (G : SimpleGraph X)
    (hsmul : ∀ (h : H) ⦃x y : X⦄, G.Adj x y → G.Adj (h • x) (h • y))
    (hconn : G.Connected) (hfree : ∀ (h : H) (x : X), h • x = x → h = 1)
    (hV : Finite (MulAction.orbitRel.Quotient H X))
    (hloc : ∀ x : X, {y : X | G.Adj x y}.Finite) : Group.FG H := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  let Q := MulAction.orbitRel.Quotient H X
  haveI : Finite Q := hV
  haveI : Fintype Q := Fintype.ofFinite Q
  -- the projection to the orbit space and a choice of representative in every orbit
  let proj : X → Q := fun x => Quotient.mk (MulAction.orbitRel H X) x
  let rep : Q → X := fun q => Quotient.out q
  have hrep : ∀ q : Q, proj (rep q) = q := fun q => Quotient.out_eq q
  -- the group element carrying `x` to the representative of its orbit
  have hex : ∀ x : X, ∃ h : H, h • x = rep (proj x) := by
    intro x
    have h : (MulAction.orbitRel H X) (rep (proj x)) x := Quotient.exact (hrep (proj x))
    exact MulAction.mem_orbit_iff.mp h
  let R : X → H := fun x => Classical.choose (hex x)
  have hR : ∀ x : X, R x • x = rep (proj x) := fun x => Classical.choose_spec (hex x)
  -- the (finite) set of candidate generators
  set S : Set H := R '' {u : X | ∃ q : Q, G.Adj (rep q) u} with hSdef
  have hSfin : S.Finite := by
    have hVV : ({u : X | ∃ q : Q, G.Adj (rep q) u} : Set X)
        = ⋃ q : Q, {u : X | G.Adj (rep q) u} := by
      ext u
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [hSdef, hVV]
    exact Set.Finite.image R (Set.finite_iUnion (fun q => hloc (rep q)))
  have memS : ∀ {u : X}, (∃ q : Q, G.Adj (rep q) u) → R u ∈ S := by
    intro u hu
    rw [hSdef]
    exact ⟨u, hu, rfl⟩
  -- key step: for adjacent vertices the two reductions differ by one of the candidates
  have key : ∀ {x y : X}, G.Adj x y → R y * (R x)⁻¹ ∈ Subgroup.closure S := by
    intro x y hxy
    have h1 : G.Adj (rep (proj x)) (R x • y) := by
      have hh := hsmul (R x) hxy
      rwa [hR x] at hh
    have hprojy : proj (R x • y) = proj y := by
      apply Quotient.sound
      exact MulAction.mem_orbit_iff.mpr ⟨R x, rfl⟩
    have hRu : R (R x • y) • (R x • y) = rep (proj y) := by
      rw [hR (R x • y), hprojy]
    have hy : y = (R y)⁻¹ • rep (proj y) := by
      rw [← hR y, inv_smul_smul]
    have hvec : (R (R x • y) * (R x * (R y)⁻¹)) • rep (proj y) = rep (proj y) := by
      rw [mul_smul, mul_smul, ← hy]
      exact hRu
    have hone : R (R x • y) * (R x * (R y)⁻¹) = 1 := hfree _ (rep (proj y)) hvec
    have hfin : R y * (R x)⁻¹ = R (R x • y) := by
      have h2 : R (R x • y) * R x = R y := by
        have h3 := hone
        rw [← mul_assoc] at h3
        rwa [mul_inv_eq_one] at h3
      rw [← h2]
      group
    rw [hfin]
    exact Subgroup.subset_closure (memS ⟨proj x, h1⟩)
  -- telescoping along a walk
  have tel : ∀ {x y : X}, (w : G.Walk x y) → R y * (R x)⁻¹ ∈ Subgroup.closure S := by
    intro x y w
    have aux : ∀ i ≤ w.length, R (w.getVert i) * (R x)⁻¹ ∈ Subgroup.closure S := by
      intro i
      induction i with
      | zero =>
          intro _
          rw [SimpleGraph.Walk.getVert_zero, mul_inv_cancel]
          exact Subgroup.one_mem _
      | succ k ih =>
          intro hk
          have hstep : R (w.getVert (k + 1)) * (R (w.getVert k))⁻¹ ∈ Subgroup.closure S :=
            key (SimpleGraph.Walk.adj_getVert_succ w (Nat.lt_of_succ_le hk))
          have hprev : R (w.getVert k) * (R x)⁻¹ ∈ Subgroup.closure S :=
            ih (Nat.le_of_succ_le hk)
          have heq : R (w.getVert (k + 1)) * (R x)⁻¹
              = (R (w.getVert (k + 1)) * (R (w.getVert k))⁻¹)
                * (R (w.getVert k) * (R x)⁻¹) := by
            group
          rw [heq]
          exact Subgroup.mul_mem _ hstep hprev
    have hL := aux w.length le_rfl
    rwa [SimpleGraph.Walk.getVert_length] at hL
  -- assemble
  have hclosure : Subgroup.closure S = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro h
    let q₀ : Q := proj x₀
    have hRv : R (rep q₀) = 1 := by
      have h1 : R (rep q₀) • rep q₀ = rep q₀ := by rw [hR (rep q₀), hrep q₀]
      exact hfree _ _ h1
    have hyproj : proj (h • rep q₀) = q₀ := by
      have h2 : proj (h • rep q₀) = proj (rep q₀) := by
        apply Quotient.sound
        exact MulAction.mem_orbit_iff.mpr ⟨h, rfl⟩
      rw [h2, hrep q₀]
    obtain ⟨w⟩ := hconn.preconnected (rep q₀) (h • rep q₀)
    have ht := tel w
    rw [hRv, inv_one, mul_one] at ht
    have hfin : R (h • rep q₀) = h⁻¹ := by
      have hmul : R (h • rep q₀) * h = 1 := by
        have h2 : (R (h • rep q₀) * h) • rep q₀ = rep q₀ := by
          rw [mul_smul, hR (h • rep q₀), hyproj]
        exact hfree _ _ h2
      exact eq_inv_of_mul_eq_one_left hmul
    rw [hfin] at ht
    simpa using Subgroup.inv_mem _ ht
  rw [Group.fg_iff]
  exact ⟨S, hclosure, hSfin⟩

end Work.WallSystem
