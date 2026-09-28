import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Rat.c2FreeMain
import Submission.Work.Rat.hopfInterfaces
import Submission.Work.Rat.finiteHomotopyRatAcyclic
import Submission.Work.Rat.finitePiRatHVanishing
import Submission.Work.Rat.U.Main
import Submission.Work.RatHurewicz.exists_bijective_piMapN_rangeModel
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Serre.serreConnectedCover
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreC0Range
import Submission.Work.Stems.CollapseDefs
import Submission.Work.Stems.homotopyFibre_conn
import Submission.Work.Serre.serreE0Range
import Submission.Work.Stems.isEMSpace_change_basepoint
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Serre.serreS2OfC0C2oddS1
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.StemsB.PiMap
import Submission.Work.Serre.serreE3a
import Submission.Work.FGThm.towerState_fibre_pi_mulEquiv
import Submission.Work.Rat.coverFibreDataSerre
import Submission.Work.Rat.wangTopRatH

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

/-- The main computation: `π_{2n-1}(Sⁿ)` is infinite for `n ≥ 2` even, from the rational
computation of the `n`-connected cover of `Sⁿ`. -/
theorem hopfCore (hE3b : Work.Serre.SerreE3b) (hFG : Work.PiS.SphereFG)
    (hT : Work.PiS.SphereTorsion)
    {n k : ℕ} (hn : 2 ≤ n) (heven : Even n) (hk : k + 1 = 2 * n) :
    Infinite (HomotopyGroup.Pi k (Work.Serre.Sph n) (Work.PiS.pt n)) := by
  -- ## Step 0: the range model and its bottom cell
  set N : ℕ := 8 * n + 8 with hNdef
  have hN : 4 * n ≤ N := by simp [hNdef]; omega
  obtain ⟨X, tX, pt, hX⟩ := Work.Serre.serreC0Range ℤ n N (by omega) (by omega)
  letI : TopologicalSpace X := tX
  obtain ⟨s₀, f, hfs₀, hbij⟩ :=
    Work.RatHurewicz.exists_bijective_piMapN_rangeModel n N hn X pt hX
  -- ## Step 1: the rational homology of the cover in degree `2n-1`
  obtain ⟨hHur, hFibVan, hFibGen⟩ :=
    coverFibreDataSerre hn heven hE3b pt N hN hX s₀ f hbij (Work.Stems.onePointSphereHomeo n)
  have hHom : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (2 * n - 1) ≅ ModuleCat.of ℚ ℚ) :=
    wangTopRatH hn _ (Work.Rat.coverProj (Work.Stems.onePointSphereHomeo n) f s₀) hHur hFibVan
      hFibGen
  -- ## Step 2: the cover is the `n`-connected cover of `Sⁿ`
  have hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
      (hX.2 0 (by omega) (Or.inr (by omega)))
  have hXconn : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) X pt) :=
    fun i hi => hX.2 i (by omega) (Or.inl hi)
  have hXkill : ∀ i : ℕ, n < i → i ≤ 4 * n + 4 → Subsingleton (HomotopyGroup (Fin i) X pt) :=
    fun i hi hiN => hX.2 i (by omega) (Or.inr (by omega))
  have hg1 : ∀ i : ℕ, i ≤ n → Function.Bijective (Work.Serre.piMapN f i s₀) := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · haveI := Work.Stems.sphereConnectivity n i hlt s₀
      haveI : Subsingleton (HomotopyGroup (Fin i) X (f s₀)) := hfs₀.symm ▸ hXconn i hlt
      exact ⟨fun a b _ => Subsingleton.elim a b,
        fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
    · subst heq
      exact hbij
  have hg2 : ∀ i : ℕ, n < i → i ≤ 4 * n + 4 → ∀ p : X,
      Subsingleton (HomotopyGroup (Fin i) X p) := by
    intro i hi hiN p
    have hsub : Subsingleton (HomotopyGroup (Fin (i - 1 + 1)) X pt) := by
      rw [show i - 1 + 1 = i from by omega]
      exact hXkill i hi hiN
    exact (show i - 1 + 1 = i from by omega) ▸
      Work.Serre.subsingleton_homotopyGroup_of_joined (hpcX.joined pt p) (i - 1) hsub
  obtain ⟨hcov1, hcov2⟩ := Work.Serre.serreConnectedCover n (4 * n + 4) (by omega) (by omega)
    (Work.Serre.Sph n) s₀ X f hg1 hg2
  -- ## Step 3: under the contrary assumption, all `π_i(E)` with `i ≤ 2n-1` are finite
  by_contra hnotinf
  have hK : k = 2 * n - 1 := by omega
  haveI hFinK : Finite (HomotopyGroup (Fin (2 * n - 1)) (Work.Serre.Sph n) (Work.PiS.pt n)) := by
    by_contra hc
    exact hnotinf (hK.symm ▸ not_finite_iff_infinite.mp hc)
  have hfinE : ∀ i : ℕ, 2 ≤ i → i ≤ 2 * n - 1 →
      Nonempty (Fintype (HomotopyGroup (Fin i)
        (Work.RatHurewicz.homotopyFibre f s₀)
        (Work.RatHurewicz.homotopyFibreBasepoint f s₀))) := by
    intro i hi2 hiM
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    by_cases hle : j + 2 ≤ n
    · haveI : Subsingleton (HomotopyGroup (Fin (j + 2))
          (Work.RatHurewicz.homotopyFibre f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := hcov1 (j + 2) hle
      exact ⟨Fintype.ofSubsingleton 1⟩
    · have hgt : n < j + 2 := Nat.lt_of_not_le hle
      have hbijmap : Function.Bijective (Work.StemsB.πmap
          (Work.RatHurewicz.homotopyFibreFst f s₀) (j + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
        Work.FGThm.πmap_homotopyFibreFst_bijective f s₀ (j + 1) (by omega)
          (hfs₀.symm ▸ hXkill (j + 2) (by omega) (by omega))
          (hfs₀.symm ▸ hXkill (j + 3) (by omega) (by omega))
      obtain ⟨γ⟩ := (Work.Serre.pathConnectedSpace_sph n (by omega)).joined (Work.PiS.pt n)
        ((Work.RatHurewicz.homotopyFibreFst f s₀) (Work.RatHurewicz.homotopyFibreBasepoint f s₀))
      obtain ⟨eγ⟩ := Work.Stems.basepoint_iso (N := Fin (j + 2)) γ
      haveI : Finite (HomotopyGroup (Fin (j + 2)) (Work.Serre.Sph n) (Work.PiS.pt n)) := by
        by_cases hik : j + 2 = 2 * n - 1
        · exact hik.symm ▸ hFinK
        · have htor : ∀ a : HomotopyGroup (Fin (j + 2)) (Work.Serre.Sph n) (Work.PiS.pt n),
              ∃ m : ℕ, 0 < m ∧ a ^ m = 1 := fun a => hT n hn j (by omega) (by omega) a
          haveI : Group.FG (HomotopyGroup (Fin (j + 2)) (Work.Serre.Sph n) (Work.PiS.pt n)) :=
            hFG n hn j
          exact CommGroup.finite_of_fg_isMulTorsion _
            (fun g => isOfFinOrder_iff_pow_eq_one.mpr (htor g))
      haveI : Finite (HomotopyGroup (Fin (j + 2)) (Work.Serre.Sph n)
          ((Work.RatHurewicz.homotopyFibreFst f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀))) :=
        Finite.of_injective (f := fun x => eγ.symm x) (fun a b h => eγ.symm.injective h)
      haveI : Finite (HomotopyGroup (Fin (j + 2))
          (Work.RatHurewicz.homotopyFibre f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
        Finite.of_injective
          (f := fun x => (MulEquiv.ofBijective _ hbijmap) x)
          (fun a b h => (MulEquiv.ofBijective _ hbijmap).injective h)
      exact ⟨Fintype.ofFinite _⟩
  -- ## Step 4: a space with finite homotopy groups in a range is rationally acyclic there
  have hzero : IsZero (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (2 * n - 1)) :=
    finitePiRatHVanishing (Work.Rat.rangeEMVanAllFin_reproved Work.Serre.serreE3a) _
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (2 * n - 1)
      (hcov1 0 (by omega)) (hcov1 1 (by omega)) hfinE (2 * n - 1) (by omega) le_rfl
  -- ## Step 5: contradiction with the non-vanishing of the rational homology
  obtain ⟨e⟩ := hHom
  haveI hQ : Subsingleton ↥(ModuleCat.of ℚ ℚ) :=
    ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso hzero e.symm)
  exact absurd (Subsingleton.elim (0 : ℚ) 1) zero_ne_one

/-- **Serre finiteness, Hopf case:** `π_{2n-1}(Sⁿ)` is infinite for `n ≥ 2` even. -/
theorem hopfInfinite (hE3b : Work.Serre.SerreE3b) (hFG : Work.PiS.SphereFG)
    (hT : Work.PiS.SphereTorsion) : Work.PiS.HopfInfinite := by
  intro n hn heven k hk
  exact hopfCore hE3b hFG hT hn heven hk

end

end Work.Rat
