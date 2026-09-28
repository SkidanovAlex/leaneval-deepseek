import Mathlib
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Serre.StableExact
import Submission.Work.Stems.homotopyFibre_conn
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Serre.periodicity_of_pairComparison
import Submission.Work.Stems.isEMSpace_change_basepoint
import Submission.Work.Stems.basepoint_iso
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Serre.serreE0Range

/-!
# The odd step of `C2` in range form

`Work.Stems.Engine.OddCoverAcyclicRange` is the *range-model* form of the odd step of the `C2`
layer: for `n` odd, `≥ 3`, `X` a **range model** of `K(ℤ,n)` through degree `N ≥ 2n-3`, and a map
`f : Sⁿ → X` bijective on `πₙ`, the homotopy fibre `E = hofib(f)` is rationally acyclic in every
degree `0 < j ≤ M` with `M ≤ 2n-4`.

This module proves it from the two inputs available in this workspace:

* `Work.Stems.Engine.C2evenRangeModelVanishing` — the even step for range models (the vanishing
  conjunct of `c2evenRangeModel`), which supplies `H_d(ΩX;ℚ) = 0` for `d < 2(n-1)-1 = 2n-3`,
  `d ∤ n-1`;
* `Work.Serre.SerreStableExact` — K5, the Serre exact sequence in the stable range
  (`H_i(E, F) ≅ H_i(Sⁿ, *; ℤ)` for `i < 2n-1`), which together with
  `H_j(Sⁿ, {s₀}; ℚ) = 0` for `j ≠ n` and the long exact sequence of the pair `(E, F)` bounds `E`
  by the fibre `F = ΩX`.

The two halves of the conclusion:

* `j ≤ n`: the cover `E` is `n`-connected (`π_k(E) = 0` for `k ≤ n`), by the long exact sequence of
  the fibration `ΩX → E → Sⁿ`: below `n` both `π_k(Sⁿ)` and `π_k(X)` vanish, and in the top degree
  `π_n(E) = 0` because `πₙ(f)` is injective.  Then `H_j(E;ℚ) = 0` for `0 < j ≤ n` by
  `Work.Serre.serreE0Range` (E0: connectivity gives rational acyclicity).
* `j > n`: `H_j(E,F;ℚ) ≅ H_j(Sⁿ,{s₀};ℚ) = 0` by K5 and the sphere pair computation, while
  `H_j(F;ℚ) = H_j(ΩX;ℚ) = 0` by the even input (the divisor condition holds because
  `n < j ≤ 2n-4` leaves no multiple of `n-1`); the long exact sequence of the pair `(E,F)` then
  gives `H_j(E;ℚ) = 0`.

The bounded connectivity statement needed in the first half is `oddCover_homotopyFibre_conn_le`
below, the range-model version of `Work.Stems.homotopyFibre_conn` (which needs the model in all
degrees, whereas a range model only supplies the degrees `< n` and `≤ N`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Stems

noncomputable section

/-- **Basepoint change for range models.**  `Work.Serre.IsEMSpaceUpTo A m N X pt` depends only on the
path component of `pt`: the `π_m`-half is transported along `Work.Stems.basepoint_iso` and the
vanishing half along `Work.Stems.subsingleton_homotopyGroup_change_basepoint`. -/
theorem oddCover_isEMSpaceUpTo_change_basepoint {A : Type} [AddCommGroup A] {m N : ℕ} (hm : 0 < m)
    {X : Type} [TopologicalSpace X] {pt x : X} (γ : Path pt x)
    (h : Work.Serre.IsEMSpaceUpTo A m hm N X pt) :
    Work.Serre.IsEMSpaceUpTo A m hm N X x := by
  have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := h.1
    obtain ⟨e'⟩ := @basepoint_iso (Fin m) X _ _ hne pt x γ
    exact ⟨e'.symm.trans e⟩
  · intro i hi hmem
    exact subsingleton_homotopyGroup_change_basepoint γ (h.2 i hi hmem)

/-- A homeomorphism induces an isomorphism of rational singular homology. -/
theorem oddCover_ratH_iso_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ Work.Serre.ratH (TopCat.of Y) n) :=
  ⟨@asIso _ _ _ _ (Work.Serre.ratHomologyMap (e.toHomotopyEquiv.toFun) n)
    (Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv n)⟩

/-- **The loop space as the fibre of the projection of the homotopy fibre.**  The fibre of
`E = hofib(f) → Sⁿ` over `s₀` is the loop space `ΩX = Path (f s₀) (f s₀)`, by the explicit inverse
pair `Work.RatHurewicz.fibrePsi`/`fibrePhi`. -/
def oddCover_fibreHomeo {X : Type} [TopologicalSpace X] {n : ℕ} (f : C(Work.Serre.Sph n, X))
    (s₀ : Work.Serre.Sph n) : Path (f s₀) (f s₀) ≃ₜ Work.RatHurewicz.fibreOf f s₀ where
  toFun := Work.RatHurewicz.fibrePsi f s₀
  invFun := Work.RatHurewicz.fibrePhi f s₀
  left_inv := Work.RatHurewicz.fibrePhi_fibrePsi f s₀
  right_inv := Work.RatHurewicz.fibrePsi_fibrePhi f s₀
  continuous_toFun := (Work.RatHurewicz.fibrePsi f s₀).continuous
  continuous_invFun := (Work.RatHurewicz.fibrePhi f s₀).continuous

/-- **Connectivity of the homotopy fibre, up to an arbitrary bound `K ≤ n`, from a range model.**
This is `Work.Stems.homotopyFibre_conn` with the model hypothesis restricted to degrees `≤ N` and
the connectivity conclusion restricted to degrees `≤ K`; the surjectivity input needed is at
degrees `≤ K + 1 ≤ N` only. -/
theorem oddCover_homotopyFibre_conn_le {X : Type} [TopologicalSpace X] {n N K : ℕ} (hn : 3 ≤ n)
    (f : C(Work.Serre.Sph n, X)) (s₀ : Work.Serre.Sph n) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hbij : Function.Bijective (Work.Serre.piMapN f n s₀))
    (hX : ∀ i, i ≠ n → i ≤ N → Subsingleton (HomotopyGroup (Fin i) X (f s₀)))
    (hKN : K + 1 ≤ N) :
    ∀ j : ℕ, j ≤ K → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre f s₀) (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  refine Work.Stems.subsingleton_homotopyFibre_of_inj_surj f K hK s₀ ?_ ?_
  · -- injectivity in degrees `≤ K`: below `n` the source `π_i(Sⁿ)` is trivial, at `n` it is `hbij`
    intro i hi
    by_cases hin : i = n
    · subst hin
      exact hbij.1
    · haveI : Subsingleton (HomotopyGroup (Fin i) (Work.Serre.Sph n) s₀) :=
        Work.Stems.sphereConnectivity n i (by omega) s₀
      exact fun a b _ => Subsingleton.elim a b
  · -- surjectivity in degrees `≤ K + 1 ≤ N`: away from `n` the target `π_i(X)` is trivial
    intro i hi
    by_cases hin : i = n
    · subst hin
      exact hbij.2
    · haveI : Subsingleton (HomotopyGroup (Fin i) X (f s₀)) := hX i hin (by omega)
      exact fun y => ⟨default, Subsingleton.elim _ y⟩

/-- **The relative term of the long exact sequence of a pair vanishes** if the absolute terms in
degrees `n` and `n - 1` do: the exactness chase in `H_n(X) → H_n(X,A) → H_{n-1}(A)` with both
outer terms zero. -/
theorem oddCover_isZero_relChainsR_homology_of_isZero_abs (R : Type) [CommRing R] (X : TopCat)
    (A : Set X) (n : ℕ) (hn : 1 ≤ n)
    (hX : IsZero ((Work.Cohomology.singularChains R X).homology n))
    (hA : IsZero ((Work.Cohomology.singularChains R (TopCat.of A)).homology (n - 1))) :
    IsZero ((Work.StemsB.relChainsR R X A).homology n) := by
  have hS := Work.StemsB.relChainsR_exact₃ R X A (n - 1)
  have hXn : IsZero ((Work.Cohomology.singularChains R X).homology ((n - 1) + 1)) :=
    IsZero.of_iso hX (eqToIso (congrArg
      (fun i => (Work.Cohomology.singularChains R X).homology i) (Nat.sub_add_cancel hn)))
  have hmid : IsZero ((Work.StemsB.relChainsR R X A).homology ((n - 1) + 1)) :=
    hS.isZero_X₂
      (hXn.eq_zero_of_src (HomologicalComplex.homologyMap
        (cokernel.π (Work.StemsB.relChainsRIncl R X A)) ((n - 1) + 1)))
      (hA.eq_zero_of_tgt (Work.StemsB.relChainsRδ R X A (n - 1)))
  exact IsZero.of_iso hmid (eqToIso (congrArg
    (fun i => (Work.StemsB.relChainsR R X A).homology i) (Nat.sub_add_cancel hn).symm))

/-- **The relative rational homology of `(Sⁿ, {s₀})` vanishes away from degree `n`** (for `n ≥ 1`,
the case needed here since the sphere in the odd step has `n ≥ 3`).  The two outer terms of the long
exact sequence of the pair both vanish: `H_i(Sⁿ;ℚ) = 0` for `0 < i ≠ n` and the point `{s₀}` is
rationally acyclic in positive degrees. -/
theorem oddCover_relH_sphere_pair (n i : ℕ) (hn : 1 ≤ n) (hi : 2 ≤ i) (hin : i ≠ n)
    (s₀ : Work.Serre.Sph n) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.Sph n))
      ({s₀} : Set (Work.Serre.Sph n))).homology i) := by
  refine oddCover_isZero_relChainsR_homology_of_isZero_abs ℚ (TopCat.of (Work.Serre.Sph n))
    ({s₀} : Set (Work.Serre.Sph n)) i (by omega) ?_ ?_
  · obtain ⟨-, h⟩ := Work.StemsB.sphRatHomology n hn
    exact h i (by omega) hin
  · exact Work.Serre.pp_isZero_absH_singleton (Work.Serre.Sph n) s₀ (by omega)

/-- **The divisor condition of the even input.**  A degree `d` with `2m+1 < d < 2(2m+1)-3` is not a
multiple of `2m`; with `n = 2m+1` (so that `2m = n-1` and `2(2m+1)-3 = 2n-3`), this is exactly the
"`d ∤ n-1`" condition of `C2evenRangeModelVanishing`. -/
theorem oddCover_divCond {m d : ℕ} (hm : 1 ≤ m) (h1 : 2 * m + 1 < d)
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

/-- **The odd step of `C2` in range form**: the cover of `Sⁿ` is rationally acyclic up to degree
`2n-4`.  See the module docstring for the two halves of the argument. -/
theorem oddCoverAcyclicRange (hEven : Work.Stems.Engine.C2evenRangeModelVanishing)
    (hK5 : Work.Serre.SerreStableExact) : Work.Stems.Engine.OddCoverAcyclicRange := by
  intro n M N hn hnodd hM hN X tX pt hXem s₀ f hbij j hj hjM
  -- write `n = 2m + 1` (`n ≥ 3` odd, so `m ≥ 1`)
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := hnodd
  have hm1 : 1 ≤ m := by omega
  let E := Work.RatHurewicz.homotopyFibre f s₀
  let e₀ := Work.RatHurewicz.homotopyFibreBasepoint f s₀
  let p : C(E, Work.Serre.Sph (2 * m + 1)) := Work.RatHurewicz.homotopyFibreFst f s₀
  -- `X` is path connected, and a range model of `K(ℤ,2m+1)` at the base point `f s₀` as well
  have hpc : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
      (hXem.2 0 (by omega) (Or.inr (by omega)))
  obtain ⟨γ⟩ := hpc.joined pt (f s₀)
  have hXem' : Work.Serre.IsEMSpaceUpTo ℤ (2 * m + 1) (by omega) N X (f s₀) :=
    oddCover_isEMSpaceUpTo_change_basepoint (m := 2 * m + 1) (N := N) (by omega) γ hXem
  have hX : ∀ i, i ≠ 2 * m + 1 → i ≤ N →
      Subsingleton (HomotopyGroup (Fin i) X (f s₀)) :=
    fun i hi hiN => hXem'.2 i hi (Or.inr hiN)
  by_cases hle : j ≤ 2 * m + 1
  · -- the range `0 < j ≤ n`: the cover `E` is `n`-connected, hence rationally acyclic below `n+1`
    have hconn : ∀ k : ℕ, k ≤ j → Subsingleton (HomotopyGroup (Fin k) E e₀) :=
      oddCover_homotopyFibre_conn_le (n := 2 * m + 1) (N := N) (K := j) (by omega) f s₀
        (by omega) (by omega) hbij hX (by omega)
    exact (Work.Serre.serreE0Range E e₀ j hconn) j hj (by omega)
  · -- the range `n < j ≤ 2n-4`: the pair sequence of `(E, F)` and the even input
    have hjbig : 2 * m + 1 < j := by omega
    have hm2 : 2 ≤ m := by omega
    -- the fibre `F = ΩX` of `E → Sⁿ` is `(n-2)`-connected
    have hfibconn : ∀ i < 2 * m + 1 - 1, Subsingleton (HomotopyGroup (Fin i)
        (↥{x : E | p x = s₀}) ⟨e₀, rfl⟩) := by
      intro i hi
      rcases i with _ | _ | i
      · exact Work.Serre.subsingleton_pi0_fibreOf f s₀ (hX 1 (by omega) (by omega))
      · exact Work.Serre.fibreOf_subsingleton f s₀ 0 (hX 2 (by omega) (by omega))
      · exact Work.Serre.fibreOf_subsingleton f s₀ (i + 1) (hX (i + 3) (by omega) (by omega))
    -- K5: the Serre exact sequence in the stable range, `H_j(E,F) ≅ H_j(Sⁿ,{s₀})`
    have hK5j : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p s₀) j) :=
      hK5 (E := E) (B := Work.Serre.Sph (2 * m + 1)) p
        (Work.RatHurewicz.isSerreFibration_homotopyFibreFst f s₀)
        e₀ s₀ rfl (2 * m + 1) (2 * m + 1 - 1) (by omega)
        (fun i hi => Work.Stems.sphereConnectivity (2 * m + 1) i hi s₀)
        hfibconn j (by omega)
    obtain ⟨hiso⟩ := Work.Serre.pp_nonempty_relH_iso_of_isIso_relPairMap p s₀ j hK5j
    have hrelSph : IsZero (Work.Serre.ppRelH (TopCat.of (Work.Serre.Sph (2 * m + 1)))
        ({s₀} : Set (Work.Serre.Sph (2 * m + 1))) j) :=
      oddCover_relH_sphere_pair (2 * m + 1) j (by omega) (by omega) (by omega) s₀
    have hrel : IsZero (Work.Serre.ppRelH (TopCat.of E) (p ⁻¹' {s₀}) j) :=
      IsZero.of_iso hrelSph hiso
    -- the fibre `F ≅ ΩX` has vanishing rational homology in degree `j` (`C2evenRange`)
    have hΩ : IsZero (Work.Serre.ratH (TopCat.of (Path (f s₀) (f s₀))) j) :=
      hEven m hm2 (N - 1) (by omega) (Path (f s₀) (f s₀)) (Path.refl (f s₀))
        (Work.Stems.isEMSpaceUpTo_loop (A := ℤ) (k := 2 * m) (by omega) (f s₀) hXem')
        j (by omega) (oddCover_divCond hm1 hjbig (by omega))
    obtain ⟨hhomeo⟩ := oddCover_ratH_iso_of_homeo (oddCover_fibreHomeo f s₀) j
    have hF : IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.fibreOf f s₀)) j) :=
      IsZero.of_iso hΩ hhomeo.symm
    -- the long exact sequence of the pair `(E, F)`
    exact Work.Serre.pp_isZero_absH_of_isZero_rel E (p ⁻¹' {s₀}) j hF hrel

end

end Work.Stems
