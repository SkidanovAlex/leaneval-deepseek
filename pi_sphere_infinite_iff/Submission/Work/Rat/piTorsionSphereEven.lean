import Mathlib
import Submission.Work.Rat.sphereOdd
import Submission.Work.Rat.s1Sphere
import Submission.Work.Rat.coverRatHEven
import Submission.Work.Rat.torsionAboveHoleE3b

/-!
# The even spheres: `π_k(Sⁿ)` is torsion for `k ≠ n`, `n` even, `k ≠ 2n-1`

`n` is even, `k ≠ n` and `k ≠ 2n-1`; we must show that every class of `π_k(Sⁿ)` has finite order.

* For `k < n` this is the connectivity of the sphere.

* For `n < k`, take a range model `X` of `K(ℤ,n)` through degree `N ≫ k`
  (`Work.Serre.serreC0Range`), the bottom cell `f : Sⁿ → X` (`πₙ`-bijective,
  `Work.RatHurewicz.exists_bijective_piMapN_rangeModel`) and the homotopy fibre
  `E = hofib f` — the `n`-connected cover of `Sⁿ`.  By `Work.Rat.coverRatHEven`,
  `H̃_j(E;ℚ) = 0` for `j ≤ k`, `j ≠ 2n-1`, and `H_{2n-1}(E;ℚ) ≅ ℚ`.

  - If `k ≤ 2n-2`, the vanishing Hurewicz theorem (`Work.Rat.piTorsion_of_ratH_vanishing_full'`)
    makes `π_k(E)` torsion, and `π_k(E) ≅ π_k(Sⁿ)` by the long exact sequence of the cover.
  - If `k ≥ 2n` (and `k ≠ 2n-1`), the class below the hole is torsion (again by the vanishing
    Hurewicz theorem, up to degree `2n-2`) and `Work.Rat.torsionAboveHoleE3b` — the far-range
    theorem, using the Gysin hypothesis `hE3b` — propagates the torsion above the hole `2n-1`;
    the transfer to `Sⁿ` is the same.
-/

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option linter.style.haveILetI false

theorem piTorsionSphereEven (hE3b : Work.Serre.SerreE3b) (hFG : Work.PiS.SphereFG)
    (hodd : ∀ (n k : ℕ), 3 ≤ n → Odd n → 2 ≤ k → k ≠ n →
      ∀ x₀ : Work.Serre.Sph n, Work.Serre.PiTorsion (Work.Serre.Sph n) x₀ (k - 1))
    (n k : ℕ) (hn : 2 ≤ n) (heven : Even n) (hk2 : 2 ≤ k) (hkn : k ≠ n) (hk2n : k ≠ 2 * n - 1)
    (x₀ : Work.Serre.Sph n) : Work.Serre.PiTorsion (Work.Serre.Sph n) x₀ (k - 1) := by
  rcases lt_trichotomy k n with hlt | heq | hgt
  · -- ## k < n
    intro a
    refine ⟨1, one_pos, ?_⟩
    haveI : Subsingleton (HomotopyGroup (Fin ((k - 1) + 1)) (Work.Serre.Sph n) x₀) :=
      (show (k - 1) + 1 = k from by omega) ▸
        (Work.Stems.sphereConnectivity n k hlt x₀)
    rw [Subsingleton.elim a 1, one_pow]
  · exact absurd heq hkn
  · -- ## k > n
    set N : ℕ := k + 4 * n + 8 with hNdef
    obtain ⟨X, tX, pt, hX⟩ := Work.Serre.serreC0Range ℤ n N (by omega) (by omega)
    letI : TopologicalSpace X := tX
    obtain ⟨s₀, f, hfs₀, hbij⟩ :=
      Work.RatHurewicz.exists_bijective_piMapN_rangeModel n N hn X pt hX
    -- ## the rational homology of the cover, from `coverRatHEven`
    have hcovRat := coverRatHEven hn heven hE3b pt N k (by omega) hX s₀ f hbij
    have hvan : ∀ i : ℕ, 0 < i → i ≤ k → i ≠ 2 * n - 1 →
        CategoryTheory.Limits.IsZero
          (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) i) := hcovRat.1
    have hgen : Nonempty (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (2 * n - 1)
        ≅ ModuleCat.of ℚ ℚ) := hcovRat.2
    -- ## the cover is the `n`-connected cover of `Sⁿ`
    have hpcX : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
        (hX.2 0 (by omega) (Or.inr (by omega)))
    have hXconn : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) X pt) :=
      fun i hi => hX.2 i (by omega) (Or.inl hi)
    have hg1 : ∀ i : ℕ, i ≤ n → Function.Bijective (Work.Serre.piMapN f i s₀) := by
      intro i hi
      rcases lt_or_eq_of_le hi with hlt' | heq'
      · haveI := Work.Stems.sphereConnectivity n i hlt' s₀
        haveI : Subsingleton (HomotopyGroup (Fin i) X (f s₀)) := hfs₀.symm ▸ hXconn i hlt'
        exact ⟨fun a b _ => Subsingleton.elim a b,
          fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
      · subst heq'
        exact hbij
    have hg2 : ∀ i : ℕ, n < i → i ≤ N → ∀ p : X,
        Subsingleton (HomotopyGroup (Fin i) X p) := by
      intro i hi hiN p
      have hsub : Subsingleton (HomotopyGroup (Fin ((i - 1) + 1)) X pt) :=
        Work.Serre.subsingleton_homotopyGroup_of_index_eq (a := i) (b := (i - 1) + 1)
          (by omega) (hX.2 i (by omega) (Or.inr hiN))
      exact (show i - 1 + 1 = i from by omega) ▸
        Work.Serre.subsingleton_homotopyGroup_of_joined (hpcX.joined pt p) (i - 1) hsub
    obtain ⟨hcov1, hcov2⟩ := Work.Serre.serreConnectedCover n N (by omega : 1 ≤ n) (by omega)
      (Work.Serre.Sph n) s₀ X f hg1 hg2
    -- ## finite generation of the homotopy groups of the cover
    have hfgE : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ k →
        Group.FG (HomotopyGroup (Fin a) (Work.RatHurewicz.homotopyFibre f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
      intro a _ haM
      by_cases hle : a ≤ n
      · haveI : Subsingleton (HomotopyGroup (Fin a) (Work.RatHurewicz.homotopyFibre f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := hcov1 a hle
        haveI : Finite (HomotopyGroup (Fin a) (Work.RatHurewicz.homotopyFibre f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := Finite.of_subsingleton
        exact Group.fg_iff_monoid_fg.mpr Monoid.fg_of_finite
      · have hlt' : n < a := Nat.lt_of_not_le hle
        have hbijmap : Function.Bijective (Work.StemsB.πmap
            (Work.RatHurewicz.homotopyFibreFst f s₀) (a - 1)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
          hcov2 a hlt' (by omega)
        haveI : Nonempty (Fin ((a - 1) + 1)) := ⟨⟨0, by omega⟩⟩
        let ee : HomotopyGroup (Fin ((a - 1) + 1))
              (Work.RatHurewicz.homotopyFibre f s₀)
              (Work.RatHurewicz.homotopyFibreBasepoint f s₀) ≃*
            HomotopyGroup (Fin ((a - 1) + 1)) (Work.Serre.Sph n) s₀ :=
          MulEquiv.ofBijective _ hbijmap
        haveI hsphere : Group.FG (HomotopyGroup (Fin ((a - 1) + 1))
            (Work.Serre.Sph n) s₀) :=
          fg_pi_sphere_of_joined ((Work.Serre.pathConnectedSpace_sph n (by omega)).joined
            (Work.PiS.pt n) s₀) (fg_pi_sphere_base hFG hn ((a - 1) + 1) (by omega))
        have hmid : Group.FG (HomotopyGroup (Fin ((a - 1) + 1))
            (Work.RatHurewicz.homotopyFibre f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
          Group.fg_of_surjective (f := ee.symm.toMonoidHom) ee.symm.surjective
        exact fg_of_index_eq (X := Work.RatHurewicz.homotopyFibre f s₀)
          (x := Work.RatHurewicz.homotopyFibreBasepoint f s₀) (a := (a - 1) + 1) (b := a)
          (by omega) hmid
    -- ## the transfer to the sphere
    have hsphere : Work.Serre.PiTorsion (Work.Serre.Sph n) s₀ (k - 1) := by
      by_cases hk : k ≤ 2 * n - 2
      · -- ## near range: the vanishing Hurewicz theorem applied to the cover
        have hnear := Work.Rat.piTorsion_of_ratH_vanishing_full' Work.Serre.serreE3a (n + 1)
          (by omega) (Work.RatHurewicz.homotopyFibre f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀) k
          (fun i hi => hcov1 i (by omega))
          (fun a _ ha => hfgE a ha)
          (fun i hi1 hi2 => hvan i (by omega) (by omega) (by omega))
        have hEt : Work.Serre.PiTorsion (Work.RatHurewicz.homotopyFibre f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (k - 1) :=
          hnear k (by omega) le_rfl
        exact Work.Serre.piTorsion_of_surjective_hom
          (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (k - 1)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀))
          (hcov2 k hgt (by omega)).2 hEt
      · -- ## far range
        have hkge : 2 * n ≤ k := by omega
        -- the torsion below the hole
        have htorsE : ∀ i : ℕ, 2 ≤ i → i < 2 * n - 1 → Work.Serre.PiTorsion
            (Work.RatHurewicz.homotopyFibre f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (i - 1) := by
          intro i hi2 hid
          by_cases hin : i ≤ n
          · haveI : Subsingleton (HomotopyGroup (Fin ((i - 1) + 1))
                (Work.RatHurewicz.homotopyFibre f s₀)
                (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) :=
              Work.Serre.subsingleton_homotopyGroup_of_index_eq (a := i) (b := (i - 1) + 1)
                (by omega) (hcov1 i hin)
            intro a
            exact ⟨1, one_pos, by rw [Subsingleton.elim a 1, one_pow]⟩
          · have hnear := Work.Rat.piTorsion_of_ratH_vanishing_full' Work.Serre.serreE3a (n + 1)
              (by omega) (Work.RatHurewicz.homotopyFibre f s₀)
              (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (2 * n - 2)
              (fun i' hi' => hcov1 i' (by omega))
              (fun a _ ha => hfgE a (by omega))
              (fun i' hi1 hi2 => hvan i' (by omega) (by omega) (by omega))
            exact hnear i (by omega) (by omega)
        have hmain := torsionAboveHoleE3b hE3b (d := 2 * n - 1) (M := k)
          (hd := by omega) (hodd := ⟨n - 1, by omega⟩)
          (X := Work.RatHurewicz.homotopyFibre f s₀)
          (x₀ := Work.RatHurewicz.homotopyFibreBasepoint f s₀)
          (h01 := hcov1 0 (by omega)) (h1 := hcov1 1 (by omega))
          (htors := htorsE)
          (hSph := fun y₀ => hodd (2 * n - 1) (2 * n) (by omega) ⟨n - 1, by omega⟩
            (by omega) (by omega) y₀)
          (hfg := hfgE) (hvan := hvan) (hgen := hgen)
        have hEt : Work.Serre.PiTorsion (Work.RatHurewicz.homotopyFibre f s₀)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀) (k - 1) :=
          hmain k (by omega) le_rfl
        exact Work.Serre.piTorsion_of_surjective_hom
          (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀) (k - 1)
            (Work.RatHurewicz.homotopyFibreBasepoint f s₀))
          (hcov2 k hgt (by omega)).2 hEt
    exact Work.Serre.piTorsion_of_joined (k - 1)
      ((Work.Serre.pathConnectedSpace_sph n (by omega)).joined
        ((Work.RatHurewicz.homotopyFibreFst f s₀)
          (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) x₀) hsphere

end

end Work.Rat
