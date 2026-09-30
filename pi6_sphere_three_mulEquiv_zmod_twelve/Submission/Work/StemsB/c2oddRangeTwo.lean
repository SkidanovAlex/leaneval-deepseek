import Mathlib
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.StemsB.serreStableExactTwo
import Submission.Work.Serre.periodicity_of_pairComparison
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.serreS2OfC0C2oddS1
import Submission.Work.Stems.isEMSpace_loop
import Submission.Work.Stems.basepoint_iso
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Stems.homotopyFibre_conn
import Submission.Work.Stems.isZero_relChainsR_sphere_pair
import Submission.Work.Stems.isEMSpace_change_basepoint

/-!
# `C2oddRange` from `C2evenRange` and the Serre exact sequence in the stable range

See `Submission/Work/Stems/C2ODD_PLAN.md` §3.  For odd `n`, a model `X` of `K(ℤ,n)` and a map
`f : Sⁿ → X` inducing a bijection on `πₙ`, the homotopy fibre `E` of `f` is rationally acyclic
below `2n-3`:

* `E` is `n`-connected (the long exact sequence of the pair `(X, Sⁿ)`,
  `Work.Stems.homotopyFibre_conn`), so `H_j(E;ℚ) = 0` for `0 < j ≤ n`
  (`Work.Serre.serreE0Range`);
* for `n < j < 2n-3`, the Serre exact sequence in the stable range
  (`Work.Serre.SerreStableExact`, applied to the Serre fibration `E → Sⁿ` with fibre
  `F = ΩX`) identifies `H_j(E, F; ℚ)` with `H_j(Sⁿ, *; ℚ) = 0`
  (`Work.Stems.isZero_relChainsR_sphere_pair`); since `H_j(F;ℚ) = 0` in the range
  (`C2evenRange` applied to the `K(ℤ,n-1)`-model `ΩX`), the long exact sequence of the pair
  gives `H_j(E;ℚ) = 0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

/-- **A homeomorphism induces an isomorphism of rational singular homology.**  (The homotopy
equivalence attached to a homeomorphism induces a rational homology isomorphism
`Work.Serre.IsRatHomologyIso.of_homotopyEquiv`.) -/
theorem c2odd_ratH_iso_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ Work.Serre.ratH (TopCat.of Y) n) :=
  ⟨@asIso _ _ _ _ (Work.Serre.ratHomologyMap (e.toHomotopyEquiv.toFun) n)
    (Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv n)⟩

/-- **The loop space as the fibre of the projection of the homotopy fibre.**  The fibre of
`E = hofib(f) → Sⁿ` over `s₀` is the loop space `ΩX = Path (f s₀) (f s₀)`, by the explicit
inverse pair `Work.RatHurewicz.fibrePsi`/`fibrePhi`. -/
def c2odd_fibreHomeo {X : Type} [TopologicalSpace X] {n : ℕ} (f : C(Work.Serre.Sph n, X))
    (s₀ : Work.Serre.Sph n) :
    Path (f s₀) (f s₀) ≃ₜ Work.RatHurewicz.fibreOf f s₀ where
  toFun := Work.RatHurewicz.fibrePsi f s₀
  invFun := Work.RatHurewicz.fibrePhi f s₀
  left_inv := Work.RatHurewicz.fibrePhi_fibrePsi f s₀
  right_inv := Work.RatHurewicz.fibrePsi_fibrePhi f s₀
  continuous_toFun := (Work.RatHurewicz.fibrePsi f s₀).continuous
  continuous_invFun := (Work.RatHurewicz.fibrePhi f s₀).continuous

/-- **The divisor condition of `C2evenRange`**, in the index shape `n = 2m+1` needed below: a
degree strictly between `n` and `2n-3` is not a multiple of `n-1 = 2m`. -/
theorem c2odd_divCond {m d : ℕ} (hm : 1 ≤ m) (h1 : 2 * m + 1 < d)
    (h2 : d < 2 * (2 * m + 1) - 3) : ∀ k : ℕ, d ≠ 2 * m * k := by
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0; simp at hk; omega
  · by_cases hk1 : k = 1
    · subst hk1; simp at hk; omega
    · have hk2 : 2 ≤ k := by omega
      have h3 : 2 * (2 * m) ≤ (2 * m) * k := by
        calc 2 * (2 * m) = (2 * m) * 2 := by ring
          _ ≤ (2 * m) * k := Nat.mul_le_mul_left _ hk2
      omega

/-- **The `C2evenRange` input.**  If `X` is a model of `K(ℤ,2m+1)`, the loop space `ΩX` (a model of
`K(ℤ,2m)`) has vanishing rational homology in degrees `2m+1 < d < 2(2m+1)-3`, which is exactly the
range `C2evenRange m` reaches. -/
theorem c2odd_isZero_ratH_loop_of_c2even (hE : Work.Stems.Engine.C2evenRange) {m : ℕ}
    (hm1 : 1 ≤ m) {X : Type} [TopologicalSpace X] (pt : X)
    (hm : Work.Serre.IsEMSpace ℤ (2 * m + 1) (by omega) X pt) {d : ℕ}
    (hd1 : 2 * m + 1 < d) (hd2 : d < 2 * (2 * m + 1) - 3) :
    IsZero (Work.Serre.ratH (TopCat.of (Path pt pt)) d) := by
  have hmodel : Work.Serre.IsEMSpace ℤ (2 * m) (by omega) (Path pt pt) (Path.refl pt) :=
    Work.Stems.isEMSpace_loop (k := 2 * m) (by omega) pt hm
  have hbound : 2 * (2 * m) - 1 = 2 * (2 * m + 1) - 3 := by omega
  exact (hE m hm1 (Path pt pt) (Path.refl pt) hmodel).2 d (by rw [hbound]; exact hd2)
    (fun k hk => c2odd_divCond hm1 hd1 hd2 k hk)

theorem c2oddRange_of_c2evenRangeTwo (hE : Work.Stems.Engine.C2evenRange) :
    Work.Stems.Engine.C2oddRange := by
  intro n hn hnodd X tX pt hXem s₀ f hbij
  -- write `n = 2m+1`; the case `m = 0` (`n = 1`) has the vacuous bound `2n-3 = 0`
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := hnodd
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    intro j hj hl
    omega
  · let E := Work.RatHurewicz.homotopyFibre f s₀
    let e₀ := Work.RatHurewicz.homotopyFibreBasepoint f s₀
    let p : C(E, Work.Serre.Sph (2 * m + 1)) := Work.RatHurewicz.homotopyFibreFst f s₀
    -- `X` is a model of `K(ℤ,n)` at the base point `f s₀` as well
    have hpc : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt (hXem.2 0 (by omega))
    obtain ⟨γ⟩ := hpc.joined pt (f s₀)
    have hXem' : Work.Serre.IsEMSpace ℤ (2 * m + 1) (by omega) X (f s₀) :=
      Work.Stems.isEMSpace_change_basepoint (by omega) γ hXem
    have hX : ∀ i, i ≠ 2 * m + 1 → Subsingleton (HomotopyGroup (Fin i) X (f s₀)) :=
      fun i hi => hXem'.2 i hi
    -- the homotopy fibre `E` is `n`-connected, hence rationally acyclic below `n+1`
    have hconnE : ∀ j ≤ 2 * m + 1, Subsingleton (HomotopyGroup (Fin j) E e₀) :=
      Work.Stems.homotopyFibre_conn (by omega) f s₀ hbij hX
    have hE0 : Work.Serre.RatVanishingBelow E (2 * m + 1 + 1) :=
      Work.Serre.serreE0Range E e₀ (2 * m + 1) hconnE
    intro j hj hjn
    by_cases hle : j ≤ 2 * m + 1
    · exact hE0 j hj (by omega)
    · -- the range `n < j < 2n-3`
      have hjbig : 2 * m + 1 < j := by omega
      -- the fibre `F = ΩX` of `E → Sⁿ` is `(n-2)`-connected
      have hfibconn : ∀ i < 2 * m + 1 - 1, Subsingleton (HomotopyGroup (Fin i)
          (↥{x : E | p x = s₀}) ⟨e₀, rfl⟩) := by
        intro i hi
        rcases i with _ | _ | i
        · exact Work.Serre.subsingleton_pi0_fibreOf f s₀ (hX 1 (by omega))
        · exact Work.Serre.fibreOf_subsingleton f s₀ 0 (hX 2 (by omega))
        · exact Work.Serre.fibreOf_subsingleton f s₀ (i + 1) (hX (i + 3) (by omega))
      -- the Serre exact sequence in the stable range
      have hK5j : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p s₀) j) :=
        Work.StemsB.serreStableExactTwo (E := E) (B := Work.Serre.Sph (2 * m + 1)) p
          (Work.RatHurewicz.isSerreFibration_homotopyFibreFst f s₀)
          e₀ s₀ rfl (2 * m + 1) (2 * m + 1 - 1) (by omega)
          (fun i hi => Work.Stems.sphereConnectivity (2 * m + 1) i hi s₀)
          hfibconn j (by omega)
      -- the relative rational homology of `(E, F)` vanishes in degree `j`
      obtain ⟨hiso⟩ := Work.Serre.pp_nonempty_relH_iso_of_isIso_relPairMap p s₀ j hK5j
      have hrelSph : IsZero (Work.Serre.ppRelH (TopCat.of (Work.Serre.Sph (2 * m + 1)))
          ({s₀} : Set (Work.Serre.Sph (2 * m + 1))) j) :=
        Work.Stems.isZero_relChainsR_sphere_pair (2 * m + 1) j (by omega) (by omega) s₀
      have hrel : IsZero (Work.Serre.ppRelH (TopCat.of E) (p ⁻¹' {s₀}) j) :=
        IsZero.of_iso hrelSph hiso
      -- the fibre `F ≅ ΩX` has vanishing rational homology in degree `j` (`C2evenRange`)
      have hΩ : IsZero (Work.Serre.ratH (TopCat.of (Path (f s₀) (f s₀))) j) :=
        c2odd_isZero_ratH_loop_of_c2even hE hm1 (f s₀) hXem' hjbig hjn
      obtain ⟨hhomeo⟩ := c2odd_ratH_iso_of_homeo (c2odd_fibreHomeo f s₀) j
      have hF : IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.fibreOf f s₀)) j) :=
        IsZero.of_iso hΩ hhomeo.symm
      -- the long exact sequence of the pair `(E, F)`
      exact Work.Serre.pp_isZero_absH_of_isZero_rel E (p ⁻¹' {s₀}) j hF hrel

end Work.StemsB

namespace Work.StemsB
-- audit: is the ported theorem axiom-clean?
#print axioms Work.StemsB.c2oddRange_of_c2evenRangeTwo
end Work.StemsB
