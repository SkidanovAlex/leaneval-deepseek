import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Cohomology.sphereHomologyTop
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `π₂(S²) ≅ ℤ`

The first non-vanishing homotopy group of the `2`-sphere.  The route is the classical one:

* `S²` is `1`-connected (`Work.Stems.sphereConnectivity`), so the integral Hurewicz map
  `π₂(S²) → H₂(S²;ℤ)` is bijective (`Work.Stems.hurewicz_first_degree`);
* the Hurewicz map is additive (`Work.Stems.hurewiczMapN_mul`), which upgrades the bijection to an
  isomorphism of groups (`hurewiczMulEquivSpheres`);
* `H₂(S²;ℤ) ≅ ℤ` (`Work.Cohomology.sphereHomologyTop`).
-/

open CategoryTheory

namespace Work.Pi6.EMODD

noncomputable section

/-- **Hurewicz in the first non-vanishing degree, as a group isomorphism.**
For an `n`-connected space `X` (`n ≥ 1`), the additive Hurewicz map
`π_{n+1}(X,x) → H_{n+1}(X;ℤ)` is bijective, and additivity makes it a multiplicative equivalence. -/
theorem hurewiczMulEquivSpheres {X : Type} [TopologicalSpace X] (x : X) (n : ℕ) (hn : 1 ≤ n)
    (hconn : ∀ i : ℕ, i < n + 1 → Subsingleton (HomotopyGroup (Fin i) X x)) :
    Nonempty (HomotopyGroup (Fin (n+1)) X x ≃*
      Multiplicative ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (n+1))) := by
  have hbij : Function.Bijective (Work.Stems.hurewiczMapN (n+1) (by omega) x) :=
    Work.Stems.hurewicz_first_degree (n+1) (by omega) x hconn
  let f : HomotopyGroup (Fin (n+1)) X x →*
      Multiplicative ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (n+1)) :=
    { toFun := fun a => Multiplicative.ofAdd (Work.Stems.hurewiczMapN (n+1) (by omega) x a)
      map_one' := by
        have h := Work.Stems.hurewiczMapN_mul n x (1 : HomotopyGroup (Fin (n+1)) X x) 1
        rw [mul_one] at h
        have h2 : Work.Stems.hurewiczMapN (n+1) (by omega) x (1 : HomotopyGroup (Fin (n+1)) X x)
            + 0 = Work.Stems.hurewiczMapN (n+1) (by omega) x 1
            + Work.Stems.hurewiczMapN (n+1) (by omega) x 1 := by
          rw [add_zero]; exact h
        exact congrArg Multiplicative.ofAdd (add_left_cancel h2).symm
      map_mul' := fun a b =>
        congrArg Multiplicative.ofAdd (Work.Stems.hurewiczMapN_mul n x a b) }
  refine ⟨MulEquiv.ofBijective f ?_⟩
  constructor
  · intro a b hab
    exact hbij.1 (Multiplicative.ofAdd.injective hab)
  · intro y
    obtain ⟨a, ha⟩ := hbij.2 (Multiplicative.toAdd y)
    refine ⟨a, ?_⟩
    change Multiplicative.ofAdd (Work.Stems.hurewiczMapN (n+1) (by omega) x a) = y
    rw [ha, ofAdd_toAdd]

/-- `π₂(S²) ≅ ℤ`. (Route: `Work.Stems.sphereConnectivity` makes `S²` `1`-connected, so the Hurewicz map `π₂(S²) → H₂(S²;ℤ)` is bijective (`Work.Stems.hurewicz_first_degree`), its additivity `Work.Stems.hurewiczMapN_mul` upgrades the bijection to a group isomorphism, and `Work.Cohomology.sphereHomologyTop` identifies `H₂(S²;ℤ) ≅ ℤ`.) -/
theorem sphTwoPi :
    Nonempty (HomotopyGroup (Fin 2) (Work.PiS.Sph 2) (Work.PiS.pt 2) ≃* Multiplicative ℤ) := by
  have hconn : ∀ i : ℕ, i < 1 + 1 →
      Subsingleton (HomotopyGroup (Fin i) (Work.Stems.sphere 2) (Work.PiS.pt 2)) :=
    fun i hi => Work.Stems.sphereConnectivity 2 i (by omega) (Work.PiS.pt 2)
  obtain ⟨e⟩ := hurewiczMulEquivSpheres (X := Work.Stems.sphere 2) (Work.PiS.pt 2) 1 le_rfl hconn
  obtain ⟨h⟩ := Work.Cohomology.sphereHomologyTop 2 (by norm_num)
  exact ⟨e.trans (AddEquiv.toMultiplicative h.toLinearEquiv.toAddEquiv)⟩

end

end Work.Pi6.EMODD
