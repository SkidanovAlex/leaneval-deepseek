import Mathlib
import Submission.Work.Rat.oddCoverAcyclicFull
import Submission.Work.Rat.s1Sphere
import Submission.Work.Serre.serreC0Range
import Submission.Work.Serre.serreE3a
import Submission.Work.RatHurewicz.exists_bijective_piMapN_rangeModel
import Submission.Work.Stems.oddCoverAcyclicRange
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Serre.serreS2OfC0C2oddS1
import Submission.Work.PiS.Interfaces

/-!
# The odd spheres: `π_k(Sⁿ)` is torsion for `k ≠ n`, `n` odd

Let `n = 2j+1 ≥ 3` be odd.  Take a range model `X` of `K(ℤ,n)` through a large degree `N`, a
`π_n`-bijective map `f : Sⁿ → X`, and let `E → Sⁿ` be its homotopy fibre — the `n`-connected cover
of `Sⁿ`.  By `Work.Rat.oddCoverAcyclicFull` (the Wang-sequence computation of the cover) `E` is
rationally acyclic below `N-1`, while `π_k(E) ≅ π_k(Sⁿ)` for `n < k ≤ N-1` by the long exact
sequence of the fibration `E → Sⁿ → X`.

`Work.Rat.piTorsion_of_ratH_vanishing_full'` (the rational vanishing Hurewicz theorem, in all
degrees, for finitely generated homotopy) applied to `E` then gives that `π_k(E)` — hence `π_k(Sⁿ)`
— is torsion for every `k > n`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Rat

noncomputable section

/-- **`π_{n+2}(E) ≅ π_{n+2}(Sᵏ)` for the `k`-connected cover** (`Work.Stems.piMap_homotopyFibreFst_bijective`,
copied here because its module is caught in the `chainMap_comp'` import cycle). -/
theorem piMap_homotopyFibreFst_bijective {Z : Type} [TopologicalSpace Z] {k N n : ℕ} (hk : 2 ≤ k)
    (f : C(Work.Serre.Sph k, Z)) (s₀ : Work.Serre.Sph k)
    (hmodel : ∀ j : ℕ, j ≤ N → j ≠ k → Subsingleton (HomotopyGroup (Fin j) Z (f s₀)))
    (hn1 : k - 1 ≤ n) (hn2 : n + 3 ≤ N) :
    Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (n + 1)
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  obtain ⟨del, d, h1, h2, _h3, _h4⟩ := Work.RatHurewicz.pair_les f s₀ n (by omega)
  constructor
  · intro x y hxy
    have hker : Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (n + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    obtain ⟨u, hu⟩ := (h1 (x * y⁻¹)).mp hker
    have hu1 : u = 1 := (hmodel (n + 3) (by omega) (by omega)).elim u 1
    have : x * y⁻¹ = 1 := by rw [← hu, hu1, map_one]
    exact mul_inv_eq_one.mp this
  · intro y
    have hy : Work.StemsB.πmap f (n + 1) s₀ y = 1 :=
      (hmodel (n + 2) (by omega) (by omega)).elim _ 1
    obtain ⟨x, hx⟩ := (h2 y).mp hy
    exact ⟨x, hx⟩

/-- Finitely generated homotopy groups of the sphere are independent of the base point. -/
theorem fg_pi_sphere_of_joined {n a : ℕ} [Nonempty (Fin a)] {x y : Work.Serre.Sph n}
    (h : Joined x y) (H : Group.FG (HomotopyGroup (Fin a) (Work.Serre.Sph n) x)) :
    Group.FG (HomotopyGroup (Fin a) (Work.Serre.Sph n) y) := by
  obtain ⟨γ⟩ := h
  obtain ⟨e⟩ := Work.Stems.basepoint_iso (N := Fin a) (X := Work.Serre.Sph n) γ
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

/-- `π_a(Sⁿ)` is finitely generated at the challenge's base point. -/
theorem fg_pi_sphere_base (hFG : Work.PiS.SphereFG) {n : ℕ} (hn : 2 ≤ n) (a : ℕ) (ha : 2 ≤ a)
    [Nonempty (Fin a)] :
    Group.FG (HomotopyGroup (Fin a) (Work.Serre.Sph n) (Work.PiS.pt n)) := by
  have h1 := hFG n hn (a - 2)
  exact fg_of_index_eq (X := Work.Serre.Sph n) (x := Work.PiS.pt n)
    (by omega : (a - 2) + 2 = a) h1

/-- `π_a(Sⁿ)` is finitely generated at any base point joined to `Work.PiS.pt n`. -/
theorem fg_pi_sphere (hFG : Work.PiS.SphereFG) {n : ℕ} (hn : 2 ≤ n) {x : Work.Serre.Sph n}
    (hx : Joined (Work.PiS.pt n) x) (a : ℕ) (ha : 2 ≤ a) [Nonempty (Fin a)] :
    Group.FG (HomotopyGroup (Fin a) (Work.Serre.Sph n) x) :=
  fg_pi_sphere_of_joined hx (fg_pi_sphere_base hFG hn a ha)

/-- **The odd spheres.**  For odd `n ≥ 3` and `k ≥ 2`, `k ≠ n`, the group `π_k(Sⁿ)` is torsion. -/
theorem piTorsion_sphere_odd (hE3b : Work.Serre.SerreE3b) (hFG : Work.PiS.SphereFG)
    (n k : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (hk2 : 2 ≤ k) (hkn : k ≠ n)
    (x₀ : Work.Serre.Sph n) :
    Work.Serre.PiTorsion (Work.Serre.Sph n) x₀ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := hodd
  have hj : 1 ≤ j := by omega
  set M : ℕ := k with hM
  set N : ℕ := M + (2 * j + 1) + 4 with hN
  obtain ⟨X, tX, pt, hX⟩ := Work.Serre.serreC0Range ℤ (2 * j + 1) N (by omega) (by omega)
  letI : TopologicalSpace X := tX
  obtain ⟨s₀, f, hfs₀, hbij⟩ :=
    Work.RatHurewicz.exists_bijective_piMapN_rangeModel (2 * j + 1) N (by omega) X pt hX
  set E : Type := Work.RatHurewicz.homotopyFibre f s₀ with hEdef
  set e₀ : E := Work.RatHurewicz.homotopyFibreBasepoint f s₀ with he0def
  -- the cover is rationally acyclic below `N-1`
  have hacyc : Work.Serre.RatAcyclicBelow E (N - 1) :=
    Work.Rat.oddCoverAcyclicFull hE3b Work.Serre.serreE3a j hj N X pt hX s₀ f hbij
  -- the model vanishes away from `n`
  have hX' : ∀ i, i ≠ 2 * j + 1 → i ≤ N → Subsingleton (HomotopyGroup (Fin i) X (f s₀)) :=
    fun i hi hiN => hfs₀ ▸ hX.2 i hi (Or.inr hiN)
  -- `E` is `n`-connected
  have hconn : ∀ i, i < 2 * j + 1 + 1 → Subsingleton (HomotopyGroup (Fin i) E e₀) :=
    fun i hi => Work.Stems.oddCover_homotopyFibre_conn_le (n := 2 * j + 1) (N := N) (K := 2 * j + 1)
      (by omega) f s₀ (by omega) le_rfl hbij hX' (by omega) i (by omega)
  -- a path from `Work.PiS.pt n` to `s₀`
  have hpath : Joined (Work.PiS.pt (2 * j + 1)) s₀ :=
    (Work.Serre.pathConnectedSpace_sph (2 * j + 1) (by omega)).joined _ _
  -- the homotopy groups of `E` in the range are finitely generated
  have hfg : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a) E e₀) := by
    intro a _ haM
    rcases lt_or_ge (2 * j + 1) a with hlt | hle
    · have hbijE : Function.Bijective
          (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) ((a - 2) + 1) e₀) :=
        piMap_homotopyFibreFst_bijective (Z := X) (k := 2 * j + 1) (N := N) (n := a - 2)
          (by omega) f s₀ (fun i hiN hin => hX' i hin hiN) (by omega) (by omega)
      haveI : Nonempty (Fin ((a - 2) + 1 + 1)) := ⟨⟨0, by omega⟩⟩
      let ee : HomotopyGroup (Fin ((a - 2) + 1 + 1)) E e₀ ≃*
          HomotopyGroup (Fin ((a - 2) + 1 + 1)) (Work.Serre.Sph (2 * j + 1)) s₀ :=
        MulEquiv.ofBijective _ hbijE
      haveI hsphere : Group.FG
          (HomotopyGroup (Fin ((a - 2) + 1 + 1)) (Work.Serre.Sph (2 * j + 1)) s₀) :=
        fg_pi_sphere_of_joined hpath
          (fg_pi_sphere_base hFG (by omega) ((a - 2) + 1 + 1) (by omega))
      have hmid : Group.FG (HomotopyGroup (Fin ((a - 2) + 1 + 1)) E e₀) :=
        Group.fg_of_surjective (f := ee.symm.toMonoidHom) ee.symm.surjective
      exact fg_of_index_eq (X := E) (x := e₀) (by omega : (a - 2) + 1 + 1 = a) hmid
    · haveI : Subsingleton (HomotopyGroup (Fin a) E e₀) := hconn a (by omega)
      haveI : Finite (HomotopyGroup (Fin a) E e₀) := Finite.of_subsingleton
      exact Group.fg_iff_monoid_fg.mpr Monoid.fg_of_finite
  -- vanishing of the rational homology of `E` below `M`
  have hhom : ∀ i, 2 * j + 1 + 1 ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of E) i) :=
    fun i hi1 hi2 => hacyc.1 i (by omega) (by omega)
  -- the rational vanishing Hurewicz theorem
  have hEtor := piTorsion_of_ratH_vanishing_full' Work.Serre.serreE3a (2 * j + 1 + 1) (by omega)
    E e₀ M hconn hfg hhom
  -- transfer to `Sⁿ` and conclude
  have hfin : ∀ s : ℕ, 2 * j + 1 + 1 ≤ s + 2 → s + 2 ≤ M →
      Work.Serre.PiTorsion (Work.Serre.Sph (2 * j + 1)) s₀ (s + 1) := by
    intro s hs1 hsM
    have hEt := hEtor (s + 2) hs1 hsM
    have hF : Subsingleton (HomotopyGroup (Fin (s + 1)) (Work.RatHurewicz.fibreOf f s₀)
        (Work.RatHurewicz.fibreOfPt f s₀)) :=
      Work.Serre.fibreOf_subsingleton f s₀ s (hX' (s + 2) (by omega) (by omega))
    have hsurj : Function.Surjective
        (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (s + 1) e₀) :=
      Work.Serre.piMap_fst_surjective_of_fibre_trivial f s₀ s hF
    exact Work.Serre.piTorsion_of_surjective_hom
      (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (s + 1) e₀) hsurj hEt
  by_cases hlt : 2 * j + 1 < k
  · have hsphere : Work.Serre.PiTorsion (Work.Serre.Sph (2 * j + 1)) s₀ (k - 1) :=
      Work.Serre.piTorsion_of_index_eq s₀ (a := k - 2 + 1) (b := k - 1) (by omega)
        (hfin (k - 2) (by omega) (by omega))
    exact Work.Serre.piTorsion_of_joined (k - 1)
      ((Work.Serre.pathConnectedSpace_sph (2 * j + 1) (by omega)).joined s₀ x₀) hsphere
  · have hkn' : k < 2 * j + 1 := by omega
    refine fun a => ⟨1, one_pos, ?_⟩
    haveI : Subsingleton (HomotopyGroup (Fin ((k - 1) + 1)) (Work.Serre.Sph (2 * j + 1)) x₀) :=
      Work.Serre.subsingleton_homotopyGroup_of_index_eq (a := k) (b := (k - 1) + 1) (by omega)
        (Work.Stems.sphereConnectivity (2 * j + 1) k hkn' x₀)
    rw [Subsingleton.elim a 1, one_pow]

end

end Work.Rat
