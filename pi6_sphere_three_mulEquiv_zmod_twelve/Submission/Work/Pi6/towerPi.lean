import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.serreConnectedCover
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.FGThm.towerState_fibre_pi_mulEquiv
import Submission.Work.FGThm.serreFGTheorem
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! # AREA TOWER — `Work.Pi6.TowerPi` (π₆(S³) ≅ H₆(Z), connectivity of the killing tower,
   and the range models P₄, P₅)

This file proves the arena `TOWER` of the π₆(S³) ≅ ℤ/12 project: `Work.Pi6.TowerPi`
(`Submission/Work/Pi6/Interfaces.lean`).  For Postnikov data
`g₃ : S³ → P₃`, `g₄ : E → P₄`, `g₅ : Y → P₅` with `E = hofib g₃`, `Y = hofib g₄`, `Z = hofib g₅`
(the killing tower `S³⟨5⟩ → S³⟨4⟩ → S³⟨3⟩ → S³`), `TowerPi` asks for

1. `π₆(S³, s₃) ≃* Multiplicative (H₆(Z;ℤ))`;
2. `E`, `Y`, `Z` are `3`-, `4`-, `5`-connected;
3. `P₄` is a `K(ℤ/2,4)` range model through degree `12` once `H₄(E;ℤ) ≅ ℤ/2`;
4. `P₅` is a `K(ℤ/2,5)` range model through degree `12` once `H₅(Y;ℤ) ≅ ℤ/2`.

The mathematics is entirely glue (no homology computation of `E`, `Y`, `Z`) and rests on three
library results:

* **Serre's connected cover** (`Work.Serre.serreConnectedCover`): the homotopy fibre of a map which
  is a `π_i`-isomorphism for `i ≤ m` and whose target has `π_i = 0` for `m < i ≤ N` is
  `m`-connected.  `PostnikovData m N g y₀` is precisely the hypothesis pair of that theorem, so (2)
  is one instantiation per stage (`towerPi_connected`).
* **The projection of a homotopy fibre is a `π_{N+1}`-isomorphism** once `π_{N+1}` and `π_{N+2}` of
  the target vanish (`Work.FGThm.πmap_homotopyFibreFst_bijective`), which for our Postnikov data is
  the vanishing furnished by `PostnikovData` above `m`.  Chaining the three stages gives
  `π₆(S³) ≃* π₆(E) ≃* π₆(Y) ≃* π₆(Z)` (`piSixChain`).
* **Hurewicz in the first non-vanishing degree** (`Work.Stems.hurewicz_first_degree`, additivity
  `Work.Stems.hurewiczMapN_mul`): for a `5`-connected `Z` the map `π₆(Z) → H₆(Z;ℤ)` is an
  isomorphism of groups (`hurewiczMulEquiv`).

For (3) and (4) the identification `π_m(P) ≅ π_m(Y) ≅ H_m(Y;ℤ) ≅ ℤ/2` (`Y = E` for `m = 4`,
`Y = Ycov` for `m = 5`) together with the vanishing of `π_i(P)` below `m` (from `π_i(Y) = 0` and the
`π_i`-bijectivity of `g`) and above `m` (from `PostnikovData`) is packaged by
`Work.FGThm.isEMSpaceUpTo_of_rangeModel` (`isEMSpaceUpTo_of_postnikov`).
-/

open scoped Topology

namespace Work.Pi6

noncomputable section

set_option linter.style.haveILetI false

/-! ## Connectivity of the stages of the killing tower -/

/-- **The three connectivity statements of `TowerPi`, from Serre's connected cover.**

`Work.Serre.serreConnectedCover` is *exactly* the fibre statement of a Postnikov section: it takes
the `π_i`-bijectivity of `g` below `m` and the vanishing of `π_i` of the target above `m`, and
returns that the homotopy fibre is `m`-connected (together with the `π_i`-isomorphisms of the
projection above `m`, which are used for the `π_6` computation). -/
theorem towerPi_connected {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3))
    (h3 : PostnikovData 3 12 g3 s3) {P4 : Type} [TopologicalSpace P4] (g4 : C(Ecov g3, P4))
    (h4 : PostnikovData 4 12 g4 (e0 g3)) {P5 : Type} [TopologicalSpace P5]
    (g5 : C(Ycov g3 g4, P5)) (h5 : PostnikovData 5 12 g5 (y0 g3 g4)) :
    (∀ i : ℕ, i ≤ 3 → Subsingleton (HomotopyGroup (Fin i) (Ecov g3) (e0 g3))) ∧
    (∀ i : ℕ, i ≤ 4 → Subsingleton (HomotopyGroup (Fin i) (Ycov g3 g4) (y0 g3 g4))) ∧
    (∀ i : ℕ, i ≤ 5 → Subsingleton (HomotopyGroup (Fin i) (Zcov g3 g4 g5)
      (Work.RatHurewicz.homotopyFibreBasepoint g5 (y0 g3 g4)))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Work.Serre.serreConnectedCover 3 12 (by norm_num) (by norm_num) S3 s3 P3 g3
      (fun i hi => h3.1 i hi s3) h3.2).1
  · exact (Work.Serre.serreConnectedCover 4 12 (by norm_num) (by norm_num) (Ecov g3) (e0 g3) P4 g4
      (fun i hi => h4.1 i hi (e0 g3)) h4.2).1
  · exact (Work.Serre.serreConnectedCover 5 12 (by norm_num) (by norm_num) (Ycov g3 g4) (y0 g3 g4)
      P5 g5 (fun i hi => h5.1 i hi (y0 g3 g4)) h5.2).1

/-! ## Hurewicz in the first non-vanishing degree, as a group isomorphism -/

/-- **`π_{n+1}(X,x) ≃* Multiplicative H_{n+1}(X;ℤ)` for `X` `n`-connected.**

The Hurewicz map is additive (`Work.Stems.hurewiczMapN_mul`) and bijective
(`Work.Stems.hurewicz_first_degree`), so it is an isomorphism of groups onto the multiplicative
group underlying the additive group `H_{n+1}(X;ℤ)`. -/
theorem hurewiczMulEquiv {X : Type} [TopologicalSpace X] (x : X) (n : ℕ) (hn : 1 ≤ n)
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

/-! ## A Postnikov section is a range model of `K(ℤ/2,m)` -/

/-- **`IsEMSpaceUpTo (ZMod 2) m _ 12 P (g y₀)` from `H_m(Y;ℤ) ≅ ℤ/2`.**

`Y` is `(m-1)`-connected and `g : Y → P` has `π_i(g)` bijective for `i ≤ m` and `π_i(P) = 0` for
`m < i ≤ 12`.  Then `π_m(P) ≅ π_m(Y) ≅ H_m(Y;ℤ) ≅ ℤ/2` (Hurewicz, applicable as `2 ≤ m`), while
`π_i(P) = 0` for `i < m` (surjectivity of `π_i(g)` from the trivial `π_i(Y)`) and for `m < i ≤ 12`
(the Postnikov data).  This is the general form of clauses (3) and (4) of `TowerPi`, applied there
to `Y = E`, `m = 4` and `Y = Ycov`, `m = 5`. -/
theorem isEMSpaceUpTo_of_postnikov {Y P : Type} [TopologicalSpace Y] [TopologicalSpace P]
    (g : C(Y, P)) (y₀ : Y) (m : ℕ) (hm0 : 0 < m) (hm2 : 2 ≤ m)
    (hconn : ∀ i : ℕ, i < m → Subsingleton (HomotopyGroup (Fin i) Y y₀))
    (hpost : PostnikovData m 12 g y₀)
    (hiso : Nonempty (HR ℤ Y m ≃ₗ[ℤ] ZMod 2)) :
    Work.Serre.IsEMSpaceUpTo (ZMod 2) m hm0 12 P (g y₀) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · -- `π_m(P) ≅ ℤ/2`, through `π_m(Y)` (the `πmap`/`piMapN` index shift) and Hurewicz
    obtain ⟨ehur⟩ := hurewiczMulEquiv y₀ n (by omega) hconn
    obtain ⟨lin⟩ := hiso
    have hbridge : ⇑(Work.StemsB.πmap g n y₀) = Work.Serre.piMapN g (n+1) y₀ := by
      funext a
      induction a using Quotient.inductionOn with
      | h p => rfl
    have hbij : Function.Bijective (Work.StemsB.πmap g n y₀) := by
      rw [hbridge]
      exact hpost.1 (n+1) le_rfl y₀
    exact ⟨(MulEquiv.ofBijective _ hbij).symm.trans
      (ehur.trans (AddEquiv.toMultiplicative lin.toAddEquiv))⟩
  · -- vanishing of `π_i(P)`, `i ≠ m`, `i ≤ 12`
    intro i hi h
    rcases lt_trichotomy i (n+1) with hlt | heq | hgt
    · haveI := hconn i hlt
      exact (hpost.1 i (by omega) y₀).2.subsingleton
    · exact absurd heq hi
    · exact hpost.2 i hgt (by omega) (g y₀)

/-! ## The `π₆`-chain of the tower -/

/-- **Clause (1) of `TowerPi`**: `π₆(S³, s₃) ≃* Multiplicative (H₆(Z;ℤ))`.

Each projection `Z → Y → E → S³` of the tower is a `π₆`-isomorphism: it is
`Work.FGThm.πmap_homotopyFibreFst_bijective` with `N = 5`, needing `π₆ = π₇ = 0` of the Postnikov
targets `P₅`, `P₄`, `P₃`, which is `PostnikovData` with `12 ≥ 7`.  Finally `Z` is `5`-connected by
Serre's connected cover, so Hurewicz in degree `6` identifies `π₆(Z) ≃* H₆(Z;ℤ)`
(`hurewiczMulEquiv`). -/
theorem piSixChain {P3 P4 P5 : Type} [TopologicalSpace P3] [TopologicalSpace P4]
    [TopologicalSpace P5]
    (g3 : C(S3, P3)) (h3 : PostnikovData 3 12 g3 s3)
    (g4 : C(Ecov g3, P4)) (h4 : PostnikovData 4 12 g4 (e0 g3))
    (g5 : C(Ycov g3 g4, P5)) (h5 : PostnikovData 5 12 g5 (y0 g3 g4)) :
    Nonempty (HomotopyGroup.Pi 6 S3 s3 ≃* Multiplicative (HR ℤ (Zcov g3 g4 g5) 6)) := by
  -- `Z` is `5`-connected
  have hZc := (Work.Serre.serreConnectedCover 5 12 (by norm_num) (by norm_num)
      (Ycov g3 g4) (y0 g3 g4) P5 g5 (fun i hi => h5.1 i hi (y0 g3 g4)) h5.2).1
  obtain ⟨ehur⟩ := hurewiczMulEquiv
    (Work.RatHurewicz.homotopyFibreBasepoint g5 (y0 g3 g4)) 5 (by norm_num)
    (fun i hi => hZc i (by omega))
  -- the three `π₆`-isomorphisms
  have h3b : Function.Bijective (Work.StemsB.πmap
      (Work.RatHurewicz.homotopyFibreFst g3 s3) 5
      (Work.RatHurewicz.homotopyFibreBasepoint g3 s3)) :=
    Work.FGThm.πmap_homotopyFibreFst_bijective g3 s3 5 (by norm_num)
      (h3.2 6 (by omega) (by omega) (g3 s3))
      (h3.2 7 (by omega) (by omega) (g3 s3))
  have h4b : Function.Bijective (Work.StemsB.πmap
      (Work.RatHurewicz.homotopyFibreFst g4 (e0 g3)) 5
      (Work.RatHurewicz.homotopyFibreBasepoint g4 (e0 g3))) :=
    Work.FGThm.πmap_homotopyFibreFst_bijective g4 (e0 g3) 5 (by norm_num)
      (h4.2 6 (by omega) (by omega) (g4 (e0 g3)))
      (h4.2 7 (by omega) (by omega) (g4 (e0 g3)))
  have h5b : Function.Bijective (Work.StemsB.πmap
      (Work.RatHurewicz.homotopyFibreFst g5 (y0 g3 g4)) 5
      (Work.RatHurewicz.homotopyFibreBasepoint g5 (y0 g3 g4))) :=
    Work.FGThm.πmap_homotopyFibreFst_bijective g5 (y0 g3 g4) 5 (by norm_num)
      (h5.2 6 (by omega) (by omega) (g5 (y0 g3 g4)))
      (h5.2 7 (by omega) (by omega) (g5 (y0 g3 g4)))
  exact ⟨(MulEquiv.ofBijective _ h3b).symm.trans ((MulEquiv.ofBijective _ h4b).symm.trans
      ((MulEquiv.ofBijective _ h5b).symm.trans ehur))⟩

/-! ## The target -/

theorem towerPi : Work.Pi6.TowerPi := by
  intro P3 _ g3 h3 P4 _ g4 h4 P5 _ g5 h5
  obtain ⟨hE, hY, hZ⟩ := towerPi_connected g3 h3 g4 h4 g5 h5
  refine ⟨piSixChain g3 h3 g4 h4 g5 h5, hE, hY, hZ, ?_, ?_⟩
  · -- (3) `P₄` is a range model of `K(ℤ/2,4)` once `H₄(E;ℤ) ≅ ℤ/2`
    intro hiso
    exact isEMSpaceUpTo_of_postnikov g4 (e0 g3) 4 (by norm_num) (by norm_num)
      (fun i hi => hE i (by omega)) h4 hiso
  · -- (4) `P₅` is a range model of `K(ℤ/2,5)` once `H₅(Y;ℤ) ≅ ℤ/2`
    intro hiso
    exact isEMSpaceUpTo_of_postnikov g5 (y0 g3 g4) 5 (by norm_num) (by norm_num)
      (fun i hi => hY i (by omega)) h5 hiso

end

end Work.Pi6
