/-
  Subproject WilE9G / Assembly — the covering step: from the maximiser to a Lagrange point.

  Combining
  * the barrier/maximiser `exists_maximiser` (Step1),
  * the local connectivity of the fibre of a `Good` stratum
    (`Assembly.stratum_fibre_locally_connected`), and
  * the Lagrange-multiplier theorem at a local maximum (`exists_lagrange_of_localmax`, Step2),

  this file produces, for a stratum `S` of one basic `B` of `X` containing the maximiser, the
  Lagrange data `(μ, μ₀)` at that maximiser.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Step1
import Submission.Work.WilE9G.Assembly.Step2
import Submission.Work.WilE9G.Assembly.stratum_fibre_locally_connected

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

variable {n m : ℕ}

/-- The product of the strict inequalities of a basic is positive where the basic holds. -/
theorem prod_pos_of_holds (X : SemiPf (n + (1 + m))) (B : Basic (n + (1 + m)) X.r)
    {z : Fin (n + (1 + m)) → ℝ} (hz : B.holds X.c z) : 0 < eaEval X.c B.pos.prod z := by
  have h : (B.pos.map (fun g => eaEval X.c g z)).prod > 0 := by
    refine List.prod_pos ?_
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    exact hz.2 g₀ hg₀
  simpa only [eaEval, map_list_prod] using h

/-- **The Lagrange data at the maximiser.** -/
theorem lagrange_of_maximiser (X : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
    (hz₀ : z₀ ∈ X.set) (w w' : Fin (n + (1 + m)) → ℝ) (hw : w ∈ connectedComponentIn X.set z₀)
    (B : Basic (n + (1 + m)) X.r) (hBmem : B ∈ X.basics) (hB : B.holds X.c w)
    (c : Fin (1 + m) → ℝ)
    (hw'K : w' ∈ connectedComponentIn (compFibre X z₀ (projBase (Nat.le_add_right n (1 + m)) w)) w)
    (hw'B : B.holds X.c w')
    (hw'max : ∀ z, z ∈ connectedComponentIn
        (compFibre X z₀ (projBase (Nat.le_add_right n (1 + m)) w)) w →
      B.holds X.c z → weight X B c z ≤ weight X B c w')
    (S : Work.WilE9G.AmbStratum (n + (1 + m))) (hS : S.Good) (hSX : S.X.set ⊆ X.set)
    (hSB : ∀ z ∈ S.X.set, B.holds X.c z) (hw'S : w' ∈ S.X.set)
    (Phi : EAPoly (n + (1 + m)) S.X.r)
    (hPhival : ∀ z ∈ S.X.set, eaEval S.X.c Phi z = eaEval X.c B.pos.prod z)
    (hsub : ∀ z ∈ S.X.set,
      projBase (Nat.le_add_right n (1 + m)) z = projBase (Nat.le_add_right n (1 + m)) w →
      S.IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) z)
    (hnd : ∀ z ∈ S.X.set,
      projBase (Nat.le_add_right n (1 + m)) z = projBase (Nat.le_add_right n (1 + m)) w →
      ∀ (mu : Fin S.j → ℝ) (mu0 : ℝ), LagEq S Phi c z mu mu0 → LagNorm mu mu0 →
      (lagJac S Phi c z mu mu0).det ≠ 0) :
    ∃ (mu : Fin S.j → ℝ) (mu0 : ℝ),
      LagEq S Phi c w' mu mu0 ∧ LagNorm mu mu0 ∧
        (lagJac S Phi c w' mu mu0).det ≠ 0 := by
  classical
  set x : Fin n → ℝ := projBase (Nat.le_add_right n (1 + m)) w with hx
  have hw'cf : w' ∈ compFibre X z₀ x := connectedComponentIn_subset _ _ hw'K
  have hw'base : projBase (Nat.le_add_right n (1 + m)) w' = x := hw'cf.2
  have hw'comp : w' ∈ connectedComponentIn X.set z₀ := hw'cf.1
  -- base-submersivity at `w'`
  have hsub' : S.IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) w' := hsub w' hw'S hw'base
  -- the nondegeneracy at `w'`
  have hnd' : ∀ (mu : Fin S.j → ℝ) (mu0 : ℝ), LagEq S Phi c w' mu mu0 →
      LagNorm mu mu0 → (lagJac S Phi c w' mu mu0).det ≠ 0 :=
    fun mu mu0 hEq hNorm => hnd w' hw'S hw'base mu mu0 hEq hNorm
  -- the local maximality of the weight on the fibre of `S.X.set`
  have hmax : ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin (n + (1 + m)) → ℝ, z ∈ S.X.set → dist z w' < ε →
      projBase (Nat.le_add_right n (1 + m)) z = projBase (Nat.le_add_right n (1 + m)) w' →
      eaEval S.X.c Phi z * Real.exp (∑ l : Fin (1 + m), c l * z (Fin.natAdd n l))
        ≤ eaEval S.X.c Phi w'
          * Real.exp (∑ l : Fin (1 + m), c l * w' (Fin.natAdd n l)) := by
    obtain ⟨ε, hε, hε'⟩ :=
      stratum_fibre_locally_connected (Nat.le_add_right n (1 + m)) S hS hw'S hsub'
    refine ⟨ε, hε, fun z hzS hd hb => ?_⟩
    have hzB : B.holds X.c z := hSB z hzS
    have hzK : z ∈ connectedComponentIn
        (compFibre X z₀ (projBase (Nat.le_add_right n (1 + m)) w)) w := by
      set C : Set (Fin (n + (1 + m)) → ℝ) := connectedComponentIn
        (S.X.set ∩ {u | projBase (Nat.le_add_right n (1 + m)) u
          = projBase (Nat.le_add_right n (1 + m)) w'}) w' with hCdef
      have hzC : z ∈ C := hε' z hzS hd hb
      have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
      have hw'C : w' ∈ C := mem_connectedComponentIn ⟨hw'S, rfl⟩
      have hCsub : C ⊆ X.set := fun u hu => hSX (connectedComponentIn_subset _ _ hu).1
      have hCcomp : C ⊆ connectedComponentIn X.set w' :=
        hCpre.subset_connectedComponentIn hw'C hCsub
      have hCcf : C ⊆ compFibre X z₀ x := fun u hu => ⟨by
          show u ∈ connectedComponentIn X.set z₀
          rw [connectedComponentIn_eq hw'comp]
          exact hCcomp hu, by
          have h1 : projBase (Nat.le_add_right n (1 + m)) u
              = projBase (Nat.le_add_right n (1 + m)) w' :=
            (connectedComponentIn_subset _ _ hu).2
          show Fin.init (Work.WilE9.Sharp.stratProj u) = x
          rw [← projBase_eq_init_stratProj, h1, hw'base]⟩
      have hzK' : z ∈ connectedComponentIn (compFibre X z₀ x) w' :=
        hCpre.subset_connectedComponentIn hw'C hCcf hzC
      show z ∈ connectedComponentIn (compFibre X z₀ x) w
      rw [connectedComponentIn_eq hw'K]
      exact hzK'
    rw [hPhival z hzS, hPhival w' hw'S]
    exact hw'max z hzK hzB
  exact exists_lagrange_of_localmax S hS Phi c
    (fun z hzS => by rw [hPhival z hzS]; exact prod_pos_of_holds X B (hSB z hzS))
    w' hw'S hsub' hmax hnd'

end Work.WilE9G.Assembly
