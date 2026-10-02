import Mathlib
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.Serre.serreC0Range
import Submission.Work.Serre.ratSerrePairComparison
import Submission.Work.RatHurewicz.freeTorsionModel
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Stems.fin_prod_ratH_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The finitely generated case of the range-model acyclicity

`Work.StemsB.fgRangeModel_acyclic`: for `A = ℤ^r × F` with `F` finite, a range model `X` of
`K(A,k)` through degree `N` (with `2k-1 ≤ N`) has vanishing rational homology in degrees
`k < i ≤ 2k-1`, given the same statement for the free group `ℤ^r` (`hfree`, the free case) and for
finite groups (`hC3`, Serre's `C3` for finite coefficients).

The proof combines the two cases by a product:

* take range models `L` of `K(ℤ,k)` and `T` of `K(F,k)` through `N` (`Work.Serre.serreC0Range`);
* the product `(Fin r → L) × T` is a range model of `K(ℤ^r × F, k)` through `N`
  (`Work.RatHurewicz.isEMSpaceUpTo_freeTorsion`), so by the comparison of range models
  (`Work.StemsB.rangeModel_ratH_iso`) it has the same rational homology as `X`;
* its rational homology vanishes in the range: the factor `Fin r → L` is handled by `hfree`
  (through `Work.RatHurewicz.isEMSpaceUpTo_pi_fin`), the factor `T` by `hC3`, and the product by
  `productModel_ratH_vanishing` below.

The product step is where the two cases meet.  It uses the **rational stable-range Serre pair
comparison** `Work.Serre.ratSerrePairComparison` for the first projection `P × T → P` — the base
`P` is `(k-1)`-connected and the fibre `T` is `(k-1)`-connected, so `b = f = k` and the comparison
is available in all degrees `< 2k` — together with the long exact sequences of the pairs
`(P,{p₀})` and `(P × T, {p₀} × T)` (`Work.StemsB.relChainsR_exact₂/₃`).  No full Künneth formula is
needed: only the *vanishing*, and the range `(k, 2k-1]` contains no nontrivial sum of two degrees
`> k`.
-/

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The product step -/

/-- **The rational homology of a product vanishes in the range.**  Let `k ≥ 2`, let `P` and `T` be
`(k-1)`-connected spaces, suppose that `P` has vanishing rational homology in degrees
`k < j ≤ 2k-1` and that `T` has vanishing rational homology in all degrees `0 < j ≤ 2k-1`.  Then so
does the product `P × T`.

Proof: the projection `P × T → P` is a Serre fibration whose fibre `T` is `(k-1)`-connected;
`Work.Serre.ratSerrePairComparison` (the *rational* stable-range Serre exact sequence, proved in
`Submission/Work/Serre/ratSerrePairComparison.lean`) gives
`H_j(P × T, {p₀} × T;ℚ) ≅ H_j(P, {p₀};ℚ)` for `j < 2k`.  The right-hand side vanishes by `hP` and
the long exact sequence of the pair `(P, {p₀})` (a point has no homology in positive degrees); the
long exact sequence of `(P × T, {p₀} × T)`, together with the vanishing of `H_j(T;ℚ) = 0` and
`H_{j-1}(T;ℚ) = 0`, then gives `H_j(P × T;ℚ) = 0`. -/
theorem productModel_ratH_vanishing {P T : Type} [TopologicalSpace P] [TopologicalSpace T]
    (p₀ : P) (t₀ : T) (k : ℕ) (hk : 2 ≤ k)
    (hPc : Work.Serre.Conn P p₀ k) (hTc : Work.Serre.Conn T t₀ k)
    (hP : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of P) j))
    (hT : ∀ j : ℕ, 0 < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of T) j)) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (P × T)) j) := by
  intro j hj1 hj2
  -- path connectedness of the two factors and of the product
  haveI hPpc : PathConnectedSpace P :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero p₀ (hPc 0 (by omega))
  haveI hTpc : PathConnectedSpace T :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero t₀ (hTc 0 (by omega))
  haveI hPTpc : PathConnectedSpace (P × T) := inferInstance
  -- the fibre of the first projection is `π_i`-trivial for `i < k`
  have hfibπ : ∀ i : ℕ, i < k →
      Subsingleton (HomotopyGroup (Fin i) ↥(Prod.fst ⁻¹' ({p₀} : Set P)) ⟨(p₀, t₀), rfl⟩) :=
    fun i hi => Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph
      (Work.Stems.fibreHomeo P T p₀) rfl i (hTc i hi)
  haveI hfibpc : PathConnectedSpace ↥(Prod.fst ⁻¹' ({p₀} : Set P)) :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero ⟨(p₀, t₀), rfl⟩
      (hfibπ 0 (by omega))
  -- the fibre is rationally acyclic below degree `k`
  have hfibvan : ∀ i : ℕ, 0 < i → i < k →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH
        (TopCat.of (Work.StemsB.fibre (ContinuousMap.fst : C(P × T, P)) p₀)) i) := by
    intro i hi hik
    refine Work.Serre.serreE0Range _ ⟨(p₀, t₀), rfl⟩ i ?_ i hi (by omega)
    intro m hm
    exact hfibπ m (by omega)
  -- the rational stable-range Serre comparison for the projection
  obtain ⟨hiso, _⟩ := Work.Serre.ratSerrePairComparison (p := (ContinuousMap.fst : C(P × T, P)))
    ((Work.Stems.isHurewiczFibration_fst P T).isSerreFibration) p₀ k k hk (by omega)
    hPTpc hPpc (fun i hi => hPc i hi) hfibpc hfibvan
  -- the relative homology of `(P, {p₀})` vanishes in the range
  have hrelP : CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of P) ({p₀} : Set P)).homology j) := by
    have hjcast : j = j - 1 + 1 := by omega
    rw [hjcast]
    have hS := Work.StemsB.relChainsR_exact₃ ℚ (TopCat.of P) ({p₀} : Set P) (j - 1)
    have hX : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℚ (TopCat.of P)).homology (j - 1 + 1)) := by
      rw [← hjcast]
      exact hP j hj1 hj2
    have hpt : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℚ (TopCat.of ↥({p₀} : Set P))).homology (j - 1)) :=
      Work.Stems.isZero_ratH_singleton P p₀ (j := j - 1) (by omega)
    exact hS.isZero_X₂ (hX.eq_zero_of_src _) (hpt.eq_zero_of_tgt _)
  -- hence the relative homology of `(P × T, {p₀} × T)`
  have hrelPT : CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of (P × T))
        (Prod.fst ⁻¹' ({p₀} : Set P))).homology j) :=
    CategoryTheory.Limits.IsZero.of_iso hrelP (hiso j (by omega)).some
  -- the fibre `{p₀} × T` is rationally acyclic in the range
  have hfibH : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℚ
        (TopCat.of ↥(Prod.fst ⁻¹' ({p₀} : Set P)))).homology j) :=
    Work.Stems.isZero_ratH_of_homeomorph (Work.Stems.fibreHomeo P T p₀) j (hT j (by omega) hj2)
  -- the long exact sequence of the pair `(P × T, {p₀} × T)` finishes
  have hS₂ := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of (P × T))
    (Prod.fst ⁻¹' ({p₀} : Set P)) j
  exact hS₂.isZero_X₂ (hfibH.eq_zero_of_src _) (hrelPT.eq_zero_of_tgt _)

/-! ## The lemma -/

theorem fgRangeModel_acyclic
    (hfree : ∀ (r : ℕ) (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
      (Y : Type) [TopologicalSpace Y] (y : Y),
        Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) k (by omega) N Y y →
        ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
          CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Y) i))
    (hC3 : Work.StemsB.C3Finite)
    (r : ℕ) (F : Type) [AddCommGroup F] [Finite F] (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N)
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpaceUpTo ((Fin r → ℤ) × F) k (by omega) N X pt) :
    ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i) := by
  intro i hi1 hi2
  have hkN : k ≤ N := by omega
  -- range models of `K(ℤ,k)` and of `K(F,k)` through degree `N`
  obtain ⟨L, tL, l₀, hL⟩ := Work.Serre.serreC0Range ℤ k N (by omega) hkN
  letI : TopologicalSpace L := tL
  obtain ⟨T, tT, t₀, hT⟩ := Work.Serre.serreC0Range F k N (by omega) hkN
  letI : TopologicalSpace T := tT
  -- the product model is a range model of `K(ℤ^r × F, k)` through `N`
  have hprod : Work.Serre.IsEMSpaceUpTo ((Fin r → ℤ) × F) k (by omega) N ((Fin r → L) × T)
      ((fun _ => l₀), t₀) :=
    Work.RatHurewicz.isEMSpaceUpTo_freeTorsion (A := (Fin r → ℤ) × F) (F := F) k N hk hN r
      l₀ t₀ (AddEquiv.refl _) hL hT
  -- the two classical cases
  have hPEM : Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) k (by omega) N (Fin r → L) (fun _ => l₀) :=
    Work.RatHurewicz.isEMSpaceUpTo_pi_fin (by omega) r l₀ hL
  have hP : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Fin r → L)) j) :=
    fun j hj1 hj2 => hfree r k N hk hN (Fin r → L) (fun _ => l₀) hPEM j hj1 hj2
  have hTvan : ∀ j : ℕ, 0 < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of T) j) :=
    fun j hj1 hj2 => hC3 F k (by omega) N T t₀ hT j hj1 (by omega)
  -- connectivities
  have hPc : Work.Serre.Conn (Fin r → L) (fun _ => l₀) k :=
    Work.Stems.conn_fin_prod k r l₀ (fun j hj => hL.2 j (by omega) (Or.inl hj))
  have hTc : Work.Serre.Conn T t₀ k := fun j hj => hT.2 j (by omega) (Or.inl hj)
  -- the product step
  have hvan := productModel_ratH_vanishing (fun _ => l₀) t₀ k hk hPc hTc hP hTvan i hi1 hi2
  -- the comparison of range models of `K(ℤ^r × F, k)`
  obtain ⟨e⟩ := Work.StemsB.rangeModel_ratH_iso ((Fin r → ℤ) × F) k N hk X pt hX
    ((Fin r → L) × T) ((fun _ => l₀), t₀) hprod i (by omega)
  exact CategoryTheory.Limits.IsZero.of_iso hvan e

end

end Work.StemsB
