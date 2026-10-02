import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.RatHurewicz.hurewiczModTorsionFirstDegree
import Submission.Work.RatHurewicz.rationalHurewiczStable_of_range
import Submission.Work.RatHurewicz.SerreHurewicz3
import Submission.Work.RatHurewicz.stableStemsTorsion_of_stable3
import Submission.Work.Stems.HurewiczMapNatural
import Submission.Work.Stems.HurewiczNeutralAgree
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The stem induction: the rational Hurewicz theorem from the two inputs

Area **RATHUREWICZ**.  This module contains the **assembly** of the rational Hurewicz theorem in the
stable range (S3 of `Submission/Work/Drive/SERRE_BLUEPRINT.md`) from the two inputs isolated in
`S3Inputs.lean`:

* `Work.RatHurewicz.TruncationHomologyTransfer` — Serre's exact sequence in the stable range plus
  the rational homology of a `K(A,k)` below `2k`, in the form of the homology transfer of the
  truncation step (area SERRE's C2/C3 and E3(a)/E3(b));
* `Work.RatHurewicz.TowerStepData` — the data the truncation tower of *this* area produces
  (`Work.RatHurewicz.exists_killed_tower`): a range model of `K(π_kX,k)`, a `k`-connected homotopy
  fibre, and surjectivity of the fibre inclusion on `π_{n+1}`.

## The argument

`Work.RatHurewicz.hurewiczTorsionSucc_of_inputs` proves

`∀ d n k, (n+1) - k ≤ d → 2 ≤ k → n+1 ≤ 2k-2 → HurewiczTorsionSucc k n`

by induction on `d`, i.e. on the **stem** `(n+1) - k` of the degree, for a *fixed* range
hypothesis `n+1 ≤ 2k-2`.  The steps are:

* `n+1 < k`: `π_{n+1}(X) = 0` by the connectivity hypothesis — nothing to prove;
* `n+1 = k`: the classical Hurewicz theorem modulo torsion in the first non-vanishing degree,
  `Work.RatHurewicz.hurewiczModTorsionFirstDegree` (proved in this area);
* `k < n+1`: the **transfer**: the tower gives `inc : X → Z` with fibre `F := homotopyFibre inc x₀`
  that is `k`-connected, and *every* class of `π_{n+1}(X)` is the image of a class `b` of
  `π_{n+1}(F)`.  Naturality of the Hurewicz map (`Work.Stems.hurewiczMap_natural`) identifies the
  Hurewicz class of `b` with a preimage of that of `a`, so the homology transfer input makes the
  Hurewicz class of `b` torsion; the **induction hypothesis at connectivity `k+1`** (the same stem
  `(n+1)-(k+1) = (n+1)-k-1`, hence available) makes `b` torsion in `π_{n+1}(F)`; and then `a`, as
  its image, is torsion.

The induction hypothesis is used at the *same* degree `n+1` and at connectivity `k+1`, which is
what makes the range `n+1 ≤ 2k-2` descend correctly: the transfer input is available precisely in
degrees `k < n+1 ≤ 2k-2`.

## Consequences

* `Work.RatHurewicz.hurewiczModTorsionRange_of_inputs` — the range form of the theorem, i.e.
  `Work.RatHurewicz.HurewiczModTorsionRange` (the full range `n+1 ≤ 2k-2`);
* `Work.RatHurewicz.rationalHurewiczStable_of_inputs` — the drive's contract
  `Work.Drive.RationalHurewiczStable`;
* `Work.RatHurewicz.rationalHurewiczStable3_of_inputs` — the one-degree-short contract
  `Work.Drive.RationalHurewiczStable3` consumed by area THOM;
* `Work.RatHurewicz.stableStemsTorsion_of_inputs` — `Work.Drive.StableStemsTorsion` (area STEMS).
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **`πmap` is Mathlib's map on homotopy groups.**  `Work.StemsB.πmap f n x` is the bundled
homomorphism `π_{n+1}(X,x) →* π_{n+1}(Y,f x)`; its underlying function is `HomotopyGroup.map f`.
This is the bridge between the exactness statements of this area (`pair_les`, the tower) and
naturality of the Hurewicz map (`Work.Stems.hurewiczMap_natural`). -/
theorem πmap_eq_map {Y : Type} [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) (x : X) (a : HomotopyGroup (Fin (n + 1)) X x) :
    Work.StemsB.πmap f n x a = HomotopyGroup.map f a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

/-- **The rational Hurewicz statement at connectivity `k` and degree `n+1`**, in the form in which
the stem induction proves it: for a `(k-1)`-connected `X`, a class of `π_{n+1}(X,x₀)` whose
Hurewicz image is of finite order is itself of finite order. -/
def HurewiczTorsionSucc (k n : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ j < k, Subsingleton (HomotopyGroup (Fin j) X x₀)) →
    ∀ a : HomotopyGroup (Fin (n + 1)) X x₀,
      (∃ N : ℕ, 0 < N ∧ (N : ℤ) • Work.Stems.hurewiczMapN (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) x₀ a = 0) →
      ∃ N : ℕ, 0 < N ∧ a ^ N = 1

/-- The degree-`n+1` statement at connectivity `k` for a degree below the connectivity: `π_{n+1}`
of a `(k-1)`-connected space with `n+1 < k` is trivial. -/
theorem hurewiczTorsionSucc_of_lt {k n : ℕ} (hlt : n + 1 < k) : HurewiczTorsionSucc k n :=
  fun X _ x₀ hconn a _ => ⟨1, one_pos, by
    rw [pow_one]
    exact (hconn (n + 1) hlt).elim a 1⟩

/-- The degree-`n+1` statement at connectivity `k = n+1` is the classical Hurewicz theorem modulo
torsion in the first non-vanishing degree, `Work.RatHurewicz.hurewiczModTorsionFirstDegree`. -/
theorem hurewiczTorsionSucc_firstDegree {k n : ℕ} (hk : 2 ≤ k) (heq : n + 1 = k) :
    HurewiczTorsionSucc k n := by
  intro X _ x₀ hconn a ha
  exact hurewiczModTorsionFirstDegree n (by omega) X x₀
    (fun i hi => hconn i (by omega)) a ha

/-- **The stem induction.**  Given the homology transfer input and the tower data, the rational
Hurewicz statement holds at connectivity `k` and degree `n+1` whenever `2 ≤ k` and
`n+1 ≤ 2k-2`.  The induction is on the stem `(n+1) - k`, for a fixed range hypothesis. -/
theorem hurewiczTorsionSucc_of_inputs (h : TruncationHomologyTransfer) (hd : TowerStepData) :
    ∀ (d n k : ℕ), (n + 1) - k ≤ d → 2 ≤ k → n + 1 ≤ 2 * k - 2 → HurewiczTorsionSucc k n := by
  intro d
  induction d with
  | zero =>
    intro n k hle hk hr
    have hlt : n + 1 < k ∨ n + 1 = k := by omega
    rcases hlt with hlt | heq
    · exact hurewiczTorsionSucc_of_lt hlt
    · exact hurewiczTorsionSucc_firstDegree hk heq
  | succ d ih =>
    intro n k hle hk hr
    by_cases hnk : n + 1 ≤ k
    · have hlt : n + 1 < k ∨ n + 1 = k := by omega
      rcases hlt with hlt | heq
      · exact hurewiczTorsionSucc_of_lt hlt
      · exact hurewiczTorsionSucc_firstDegree hk heq
    · -- the transfer step: `k < n+1`
      have hkn : k < n + 1 := not_le.mp hnk
      intro X _ x₀ hconn a ha
      obtain ⟨Z, tZ, inc, hmodel, hfib, hsurj⟩ := hd k n hk hkn hr X x₀ hconn
      letI := tZ
      obtain ⟨b, hb⟩ := hsurj a
      have hbmap : HomotopyGroup.map (homotopyFibreFst inc x₀) b = a := by
        rw [← πmap_eq_map (homotopyFibreFst inc x₀) n (homotopyFibreBasepoint inc x₀) b]
        exact hb
      -- naturality of the Hurewicz map along the projection of the homotopy fibre
      have hnat := Work.Stems.hurewiczMap_natural (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (homotopyFibreFst inc x₀)
        (x₀ := homotopyFibreBasepoint inc x₀) b
      -- the Hurewicz class of `a` is the image of that of `b`
      have hclass : Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ a =
          HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
            (TopCat.ofHom (homotopyFibreFst inc x₀))) (n + 1)
            (Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
              (homotopyFibreBasepoint inc x₀) b) := by
        rw [← hbmap, Work.Stems.hurewiczMapN_eq_hurewiczMap,
          Work.Stems.hurewiczMapN_eq_hurewiczMap]
        exact hnat
      -- transfer the torsion of the Hurewicz class to the fibre
      obtain ⟨N, hN, hNa⟩ := ha
      have hker : ∃ M : ℕ, 0 < M ∧ M • HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of (homotopyFibre inc x₀)) (TopCat.of X)
            (TopCat.ofHom (homotopyFibreFst inc x₀))) (n + 1)
            (Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
              (homotopyFibreBasepoint inc x₀) b) = 0 := by
        refine ⟨N, hN, ?_⟩
        rw [← hclass]
        simpa [Nat.cast_smul_eq_nsmul] using hNa
      obtain ⟨M, hM, hMb⟩ :=
        h k hk X Z inc x₀ hfib hmodel n hkn hr
          (Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
            (homotopyFibreBasepoint inc x₀) b) hker
      -- the induction hypothesis at connectivity `k+1`, same degree
      obtain ⟨M', hM', hbM⟩ := ih n (k + 1) (by omega) (by omega) (by omega)
        (homotopyFibre inc x₀) (homotopyFibreBasepoint inc x₀)
        (fun j hj => hfib j (by omega)) b ⟨M, hM, by simpa [Nat.cast_smul_eq_nsmul] using hMb⟩
      refine ⟨M', hM', ?_⟩
      have hpow : (Work.StemsB.πmap (homotopyFibreFst inc x₀) n
          (homotopyFibreBasepoint inc x₀) b) ^ M' = 1 := by
        rw [← map_pow (Work.StemsB.πmap (homotopyFibreFst inc x₀) n
          (homotopyFibreBasepoint inc x₀)) b M', hbM, map_one]
      exact hb ▸ hpow

/-- **The range form of the rational Hurewicz theorem** from the two inputs, i.e. the full stable
range `n+1 ≤ 2k-2`. -/
theorem hurewiczModTorsionRange_of_inputs (h : TruncationHomologyTransfer) (hd : TowerStepData) :
    HurewiczModTorsionRange :=
  fun k hk X _ x₀ hconn n hn a ha =>
    hurewiczTorsionSucc_of_inputs h hd (n + 1) n k (by omega) hk hn X x₀ hconn a ha

/-- **The drive's contract `Work.Drive.RationalHurewiczStable`** from the two inputs. -/
theorem rationalHurewiczStable_of_inputs (h : TruncationHomologyTransfer) (hd : TowerStepData) :
    Work.Drive.RationalHurewiczStable :=
  rationalHurewiczStable_of_range (hurewiczModTorsionRange_of_inputs h hd)

/-- **The one-degree-short contract `Work.Drive.RationalHurewiczStable3`** (the form consumed by
area THOM) from the two inputs. -/
theorem rationalHurewiczStable3_of_inputs (h : TruncationHomologyTransfer) (hd : TowerStepData) :
    Work.Drive.RationalHurewiczStable3 :=
  rationalHurewiczStable3_of_range (hurewiczModTorsionRange_of_inputs h hd)

/-- **The contract of area STEMS `Work.Drive.StableStemsTorsion`** from the two inputs. -/
theorem stableStemsTorsion_of_inputs (h : TruncationHomologyTransfer) (hd : TowerStepData) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_rationalHurewiczStable3 (rationalHurewiczStable3_of_inputs h hd)

end

end Work.RatHurewicz
