import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Instances.AddCircle.Real

open Topology Function Set Filter

noncomputable section

namespace Commons.Analysis.Fourier

set_option autoImplicit false

/-- A continuous function on `ι → ℝ` which is periodic with period `ℤ` in every coordinate
descends to a continuous function on the torus `UnitAddTorus ι`.

Proof outline: the coordinatewise quotient map `q : (ι → ℝ) → UnitAddTorus ι` is an open
quotient map (a product, over the finite type `ι`, of the open quotient maps `ℝ → UnitAddCircle`),
so a function on the torus is continuous iff its pullback to `ℝ` along `q` is continuous.  The
periodicity hypothesis says exactly that `h` is constant on the fibres of `q`, hence defines a
function `g` on the torus with `g ∘ q = h`; continuity of `g` follows from that of `h`. -/
theorem torus_descent_continuous {ι : Type*} [Fintype ι]
    (h : C(ι → ℝ, ℂ))
    (hper : ∀ x : ι → ℝ, ∀ z : ι → ℤ, h (x + fun i : ι => (z i : ℝ)) = h x) :
    ∃ H : C(UnitAddTorus ι, ℂ),
      ∀ x : ι → ℝ, H (fun i : ι => (x i : UnitAddCircle)) = h x := by
  classical
  -- The coordinatewise quotient map to the torus.
  let q : (ι → ℝ) → UnitAddTorus ι := fun x i => (x i : UnitAddCircle)
  -- `q` is a product of the open quotient maps `ℝ → UnitAddCircle`, hence itself an open
  -- quotient map (and in particular a quotient map).
  have hq_open : IsOpenQuotientMap q := by
    change IsOpenQuotientMap (Pi.map (fun _ : ι => (fun r : ℝ => (r : UnitAddCircle))))
    exact IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  have hq : IsQuotientMap q := hq_open.isQuotientMap
  -- `h` is constant on the fibres of `q`: points lying over the same torus point differ by an
  -- integer-valued function, and `h` is invariant under integer translations.
  have hfib : ∀ x y : ι → ℝ, q x = q y → h x = h y := by
    intro x y hxy
    have hn : ∀ i : ι, ∃ n : ℤ, (n : ℝ) = y i - x i := by
      intro i
      have hi := (congrFun hxy i).symm
      have hd : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]
        exact hi
      have hzero : ∃ n : ℤ, n • (1 : ℝ) = y i - x i :=
        (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hd
      rcases hzero with ⟨n, hn'⟩
      refine ⟨n, ?_⟩
      simpa [zsmul_eq_mul] using hn'
    choose z hz using hn
    exact (calc
      h y = h (x + (fun i : ι => (z i : ℝ))) := by
        congr 1
        ext i
        rw [Pi.add_apply, hz i]
        ring
      _ = h x := hper x z).symm
  -- Define `g` on the torus by pushing `h` down along a choice of representatives.
  let g : UnitAddTorus ι → ℂ := fun t => h (Classical.choose (hq.surjective t))
  have hg_eq : ∀ x : ι → ℝ, g (q x) = h x := by
    intro x
    dsimp [g]
    exact (hfib x (Classical.choose (hq.surjective (q x)))
      (Classical.choose_spec (hq.surjective (q x))).symm).symm
  have hcomp : g ∘ q = h := by
    funext x
    exact hg_eq x
  -- Since `q` is a quotient map and `g ∘ q = h` is continuous, `g` is continuous.
  have hg_cont : Continuous g := by
    rw [hq.continuous_iff]
    simpa [hcomp] using h.continuous
  refine ⟨⟨g, hg_cont⟩, ?_⟩
  intro x
  simpa [q] using hg_eq x

end Commons.Analysis.Fourier