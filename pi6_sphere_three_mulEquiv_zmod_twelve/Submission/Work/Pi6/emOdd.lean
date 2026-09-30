import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMODD.Defs
import Submission.Work.Pi6.EMODD.cohHomology
import Submission.Work.Pi6.EMODD.cpowLaws
import Submission.Work.Pi6.EMODD.kOneMod
import Submission.Work.Pi6.EMODD.kTwoRing
import Submission.Work.Pi6.EMODD.finDimField
import Submission.Work.Pi6.EMODD.fibreOfMpathQ
import Submission.Work.Pi6.EMODD.ssForcing
import Submission.Work.Pi6.EMODD.piIsoTransfer
import Submission.Work.Pi6.EMODD.killEnlarge
import Submission.Work.Pi6.EMODD.survivalFibre
import Submission.Work.Pi6.EMODD.fibreH2Nonzero
import Submission.Work.Pi6.EMODD.emOddLoop
import Submission.Work.Pi6.EMM2.kZmodel
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.EMFG.finiteAbelianModelFG
import Submission.Work.SSS.serreFGThreeForTwo
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Cohomology.singularCohomology_zero
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
AREA EMODD (pi6).  Read `REFS/NOTES_LEAD_PI6.md` §4 "EMODD".

Target: `Work.Pi6.EMOdd`, i.e. for `n ∈ {2,3,4}`, a range model `X` of `K(ℤ/2,n)` through `N ≥ 10`
and an odd prime `p`, the mod-`p` homology `H_i(X;ZMod p)` vanishes for `0 < i ≤ 8`.

## The proof

Write `𝕜 := ZMod p`.

1. **`emOdd_two` (the crux, `n = 2`).**  For a range model `X` of `K(ℤ/2,2)` through `10`:
   * `Work.Pi6.EMM2.kZmodel` builds `KZ := kTower (S²) 8`, a range model of `K(ℤ,2)` through `10`,
     with a based map `r : KZ → X` onto on `π₂`, hence non-trivial on `π₂`.
   * `Work.Pi6.EMODD.fibreOfMpathQ` then makes the strict fibre
     `F = mpathFibre r k₀` of the Serre fibration `mpathQ r : mpath r → X` a range model of
     `K(ℤ,2)` through `9`, and the total `T = mpath r` a range model of `K(ℤ,2)` through `10`.
   * `Work.Pi6.EMODD.kTwoRing` (with its inputs `Work.Pi6.EMODD.kOneMod` and
     `Work.Pi6.EMODD.finDimField`) gives the mod-`𝕜` cohomology of `F` and `T` in the range: one
     dimensional in even degrees, vanishing in odd degrees, with non-zero cup powers.
   * The fibre restriction is non-zero in degree two: `Work.Pi6.EMODD.fibreH2Nonzero` (the fibre
     inclusion is `×2` on `H₂(−;ℤ) ≅ ℤ` and `2 ≠ 0` in `𝕜`).
   * `Work.Pi6.EMODD.survivalFibre` converts that into the survival hypothesis for the
     multiplicative mod-`𝕜` Serre spectral sequence (`IsSerreMSS`'s fibre edge).
   * `Work.Pi6.EMODD.ssForcing` part (B) then forces `H^s(X;𝕜) = 0` for `0 < s ≤ 8`, and
     `Work.Pi6.EMODD.isZero_cohomology_iff_subsingleton_homology` converts this back to homology.

2. **The loop steps.**  `Work.Pi6.EMODD.emOddLoop`: for a range model `X` of `K(ℤ/2,n+1)` through
   `N ≥ 10` the path–loop fibration `ΩX → PX → X` has contractible total, so if `ΩX` is
   `𝔽_p`-acyclic through degree `8` then so is `X` (`ssForcing` part (A), `N = 8`).
   This reduces `n = 3` to `n = 2` (the loop space is a `K(ℤ/2,2)`-model through `9`) and `n = 4` to
   `n = 3` (the loop space is a `K(ℤ/2,3)`-model through `9`).

3. **Thresholds.**  `emOdd_two` needs the model to be a `K(ℤ/2,2)`-range model through `10` — at
   range `9` the fibre would only be through `8` and `kTwoRing` would miss degree `8`.  Hence
   `Work.Pi6.EMODD.killEnlarge` (`KillCells m` of a `K(A,k)`-model through `m` is one through
   `m+1`) enlarges each loop space to a model through `10`, and `Work.Pi6.EMODD.piIsoTransfer`
   (the `KillCells` inclusion is a `π`-isomorphism in the range) transfers the vanishing back:

   * `acyclic_two_of_nine`: a `K(ℤ/2,2)`-model through `9` (`= ΩX` for `n = 3`, and `= ΩL1'` for
     `n = 4`) is `𝔽_p`-acyclic through degree `8`;
   * `acyclic_three_of_ten`: a `K(ℤ/2,3)`-model through `10` (the enlarged `ΩX` for `n = 4`) is
     `𝔽_p`-acyclic through degree `8`.

`K2ZFacts` is not needed: `kTwoRing` supplies all the mod-`𝕜` facts used here directly from
`MSSHolds`.
-/

open CategoryTheory CategoryTheory.Limits


namespace Work.Pi6

theorem emOddTwo (hM : Work.Pi6.MSSHolds) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (X : Type) [TopologicalSpace X] (x₀ : X)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) 10 X x₀) :
    ∀ i : ℕ, 0 < i → i ≤ 8 → Subsingleton (HR (ZMod p) X i) := by
  -- ## The K(ℤ,2)-model covering `X`
  obtain ⟨KZ, tKZ, k₀, r, hr0, hKZ, hsurj, _hsurjh, _hfib⟩ :=
    Work.Pi6.EMM2.kZmodel x₀ 10 le_rfl hX
  letI : TopologicalSpace KZ := tKZ
  have hXr : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) 10 X (r k₀) := by
    rw [hr0]; exact hX
  -- ## `π₂(r) ≠ 0`
  have hπ : ∃ a : HomotopyGroup (Fin 2) KZ k₀, Work.StemsB.πmap r 1 k₀ a ≠ 1 := by
    obtain ⟨φ⟩ := hXr.1
    have hy : φ.symm (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
      intro h
      have h1 := congrArg φ h
      rw [MulEquiv.apply_symm_apply, MulEquiv.map_one] at h1
      exact Work.Pi6.EMM2.ofAdd_one_ne_one h1
    obtain ⟨a, ha⟩ := hsurj (φ.symm (Multiplicative.ofAdd (1 : ZMod 2)))
    exact ⟨a, by rw [ha]; exact hy⟩
  -- ## the fibre and the total of the mapping-path fibration
  obtain ⟨hF, _hιπ, hT⟩ := Work.Pi6.EMODD.fibreOfMpathQ 10 le_rfl r k₀ hKZ hXr hπ
  -- ## `(2 : ZMod p) ≠ 0`
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℤ) : ZMod p) = 0 := by simpa using h
    have hd : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp h'
    have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
    have hp2' : p ≤ 2 := by exact_mod_cast hle
    exact hp2 (le_antisymm hp2' (Fact.out : Nat.Prime p).two_le)
  -- ## the fibre restriction is non-zero in degree `2`
  have hιne : (Work.Pi6.cmap (ZMod p) (Work.StemsB.fibreIncl (Work.Serre.mpathQ r)
      (Work.Serre.mpathQ r (Work.Pi6.EMODD.mpathPt r k₀))) 2).hom ≠ 0 :=
    Work.Pi6.EMODD.fibreH2Nonzero (ZMod p) h2p 10 le_rfl r k₀ hKZ hXr hπ
  -- ## finiteness
  have hfin𝕜 : Module.Finite ℤ (ZMod p) := inferInstance
  have hfin : ∀ (A : Type) [TopologicalSpace A] (N : ℕ),
      (∀ i ≤ N, Module.Finite ℤ (Work.PiS.HZ A i)) →
      ∀ q ≤ N, FiniteDimensional (ZMod p) (Work.Pi6.Coh (ZMod p) A q) :=
    fun A _ N h => Work.Pi6.EMODD.finDimField (ZMod p) hfin𝕜 A N h
  have hEM := Work.EMFG.emHomologyFG Work.SSS.serreFGThreeForTwo
  have hFGX : Work.PiS.FGUpTo X 9 := hEM (ZMod 2) 2 (by norm_num) 9 X x₀ hX
  have hFGF : Work.PiS.FGUpTo (Work.Pi6.EMODD.mpathFibre r k₀) 8 :=
    hEM ℤ 2 (by norm_num) 8 (Work.Pi6.EMODD.mpathFibre r k₀)
      (Work.Pi6.EMODD.mpathFibrePt r k₀) hF
  have hFGT : Work.PiS.FGUpTo (Work.Serre.mpath r) 9 :=
    hEM ℤ 2 (by norm_num) 9 (Work.Serre.mpath r) (Work.Pi6.EMODD.mpathPt r k₀) hT
  have hfinF : ∀ q : ℕ, q ≤ 8 → FiniteDimensional (ZMod p)
      (Work.Pi6.Coh (ZMod p) (Work.Pi6.EMODD.mpathFibre r k₀) q) :=
    fun q hq => hfin _ 8 (fun i hi => hFGF i hi) q hq
  have hfinT : ∀ q : ℕ, q ≤ 8 → FiniteDimensional (ZMod p)
      (Work.Pi6.Coh (ZMod p) (Work.Serre.mpath r) q) :=
    fun q hq => hfin _ 8 (fun i hi => hFGT i (by omega)) q hq
  have hfinX : ∀ q : ℕ, q ≤ 8 → FiniteDimensional (ZMod p) (Work.Pi6.Coh (ZMod p) X q) :=
    fun q hq => hfin _ 8 (fun i hi => hFGX i (by omega)) q hq
  -- ## the cohomology ring of `F` and `T`
  obtain ⟨wF, hFpow, hFeven, hFodd⟩ :=
    Work.Pi6.EMODD.kTwoRing (ZMod p) hM (Work.Pi6.EMODD.kOneMod p) hfin 9 (by norm_num)
      (Work.Pi6.EMODD.mpathFibre r k₀) (Work.Pi6.EMODD.mpathFibrePt r k₀) hF
  obtain ⟨wT, _hTpow, hTeven, hTodd⟩ :=
    Work.Pi6.EMODD.kTwoRing (ZMod p) hM (Work.Pi6.EMODD.kOneMod p) hfin 10 (by norm_num)
      (Work.Serre.mpath r) (Work.Pi6.EMODD.mpathPt r k₀) hT
  -- ## simple connectivity of `X`, and `H⁰(X) ≅ 𝕜`
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀
      (hX.2 0 (by norm_num) (Or.inl (by norm_num)))
  have hB0 : Nonempty (Work.Pi6.Coh (ZMod p) X 0 ≅ ModuleCat.of (ZMod p) (ZMod p)) :=
    Work.Cohomology.singularCohomology_zero (ZMod p) (TopCat.of X)
  have hSC : Work.PiS.SimplyConn X (Work.Serre.mpathQ r (Work.Pi6.EMODD.mpathPt r k₀)) := by
    have hal : Work.Serre.mpathQ r (Work.Pi6.EMODD.mpathPt r k₀) = r k₀ := rfl
    refine ⟨?_, ?_⟩
    · simpa only [hal, hr0] using hX.2 0 (by norm_num) (Or.inl (by norm_num))
    · simpa only [hal, hr0] using hX.2 1 (by norm_num) (Or.inl (by norm_num))
  -- ## the Serre spectral sequence
  obtain ⟨S, hS⟩ := hM (ZMod p) (Work.Serre.mpath r) X (Work.Serre.mpathQ r)
    (Work.Pi6.EMODD.mpathPt r k₀) 8 (Work.Serre.mpathQ_isSerreFibration r) hSC hfinF hfinX
  -- ## survival of the fibre classes
  have hsurv : ∀ q : ℕ, 2 ≤ q → q ≤ 8 → Even q → ∃ z : S.E (q + 2) (0, (q : ℤ)), z ≠ 0 :=
    Work.Pi6.EMODD.survivalFibre (ZMod p) (Work.Serre.mpathQ r) (Work.Pi6.EMODD.mpathPt r k₀) 8 S hS
      hιne hB0 (hFeven 2 (by norm_num) (by norm_num)) ⟨wF, fun k hk => hFpow k (by omega)⟩
  -- ## forcing
  have hforc : ∀ s : ℕ, 0 < s → s ≤ 8 → IsZero (Work.Pi6.Coh (ZMod p) X s) :=
    (Work.Pi6.EMODD.ssForcing (𝕜 := ZMod p)).2 (p := Work.Serre.mpathQ r)
      (e₀ := Work.Pi6.EMODD.mpathPt r k₀) (N := 8) (S := S) hS
      (fun q hq => ⟨hfinF q hq, hfinT q hq⟩) hfinX
      (fun q hq => ⟨fun he => ⟨hFeven q (by omega) he, hTeven q (by omega) he⟩,
        fun ho => ⟨hFodd q (by omega) ho, hTodd q (by omega) ho⟩⟩) hsurv
  -- ## back to homology
  intro i hi0 hi8
  exact (Work.Pi6.EMODD.isZero_cohomology_iff_subsingleton_homology (ZMod p) X i).mp
    (hforc i hi0 hi8)

/-! ## The two range-reduction helpers -/

/-- **A `K(ℤ/2,2)`-model through `9` is `𝔽_p`-acyclic through degree `8`** for every odd prime `p`:
enlarge it to a model through `10` by `KillCells 9`, apply `emOdd_two`, and transfer the vanishing
back along the `π`-isomorphism `killIncl 9 Y` (`Work.Pi6.EMODD.piIsoTransfer`). -/
theorem acyclic_two_of_nine (hM : Work.Pi6.MSSHolds) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (hY : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) 9 Y y₀) :
    ∀ i : ℕ, 0 < i → i ≤ 8 → Subsingleton (HR (ZMod p) Y i) := by
  haveI : Nonempty Y := ⟨y₀⟩
  have hY' : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) 10
      (Work.Serre.KillCells 9 Y) (Work.Serre.killIncl 9 Y y₀) :=
    Work.Pi6.EMODD.killEnlarge (ZMod 2) 2 9 (by norm_num) (by norm_num) y₀ hY
  have hem : ∀ i : ℕ, 0 < i → i ≤ 8 →
      Subsingleton (HR (ZMod p) (Work.Serre.KillCells 9 Y) i) :=
    emOddTwo hM p hp2 (Work.Serre.KillCells 9 Y) (Work.Serre.killIncl 9 Y y₀) hY'
  intro i hi0 hi8
  exact Work.Pi6.EMODD.piIsoTransfer (ZMod p) 9 (Work.Serre.killIncl 9 Y)
    (fun j hj x => (Work.Serre.killCells_step 9 Y).1 j (by omega) x)
    (fun j hj0 hj9 => hem j hj0 (by omega)) i hi0 (by omega)

/-- **A `K(ℤ/2,3)`-model through `10` is `𝔽_p`-acyclic through degree `8`**: the path–loop
fibration, with the loop space a `K(ℤ/2,2)`-model through `9` (`Work.Pi6.EMODD.emOddLoop` and
`acyclic_two_of_nine`). -/
theorem acyclic_three_of_ten (hM : Work.Pi6.MSSHolds) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (X : Type) [TopologicalSpace X] (x₀ : X)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) 10 X x₀) :
    ∀ i : ℕ, 0 < i → i ≤ 8 → Subsingleton (HR (ZMod p) X i) := by
  have hL : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) 9 (Path x₀ x₀) (Path.refl x₀) :=
    Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := 3) (M := 10) (by norm_num) x₀ hX
  exact Work.Pi6.EMODD.emOddLoop p hM 2 10 (by norm_num) (by norm_num) X x₀ hX
    (fun i hi0 hi8 => acyclic_two_of_nine hM p hp2 _ _ hL i hi0 hi8)

/-- **EMOdd.** -/
theorem emOdd (hM : Work.Pi6.MSSHolds) (hZ : Work.Pi6.K2ZFacts) : Work.Pi6.EMOdd := by
  intro n hn2 hn4 X _ x₀ N hN hX p hp hp2
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hn with rfl | rfl | rfl
  · -- `n = 2`
    exact emOddTwo hM p hp2 X x₀ (Work.EMFG.isEMSpaceUpTo_mono hX hN)
  · -- `n = 3`
    have hL : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) (N - 1)
        (Path x₀ x₀) (Path.refl x₀) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := 3) (M := N) (by norm_num) x₀ hX
    have hL9 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) 9
        (Path x₀ x₀) (Path.refl x₀) :=
      Work.EMFG.isEMSpaceUpTo_mono hL (by omega)
    exact Work.Pi6.EMODD.emOddLoop p hM 2 N (by norm_num) hN X x₀ hX
      (fun i hi0 hi8 => acyclic_two_of_nine hM p hp2 _ _ hL9 i hi0 hi8)
  · -- `n = 4`
    haveI : Nonempty (Path x₀ x₀) := ⟨Path.refl x₀⟩
    have hL1 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) (N - 1)
        (Path x₀ x₀) (Path.refl x₀) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := 4) (M := N) (by norm_num) x₀ hX
    have hL19 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) 9
        (Path x₀ x₀) (Path.refl x₀) :=
      Work.EMFG.isEMSpaceUpTo_mono hL1 (by omega)
    have hL1' : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) 10
        (Work.Serre.KillCells 9 (Path x₀ x₀))
        (Work.Serre.killIncl 9 (Path x₀ x₀) (Path.refl x₀)) :=
      Work.Pi6.EMODD.killEnlarge (ZMod 2) 3 9 (by norm_num) (by norm_num)
        (Path.refl x₀) hL19
    have hem : ∀ i : ℕ, 0 < i → i ≤ 8 →
        Subsingleton (HR (ZMod p) (Work.Serre.KillCells 9 (Path x₀ x₀)) i) :=
      acyclic_three_of_ten hM p hp2 _ _ hL1'
    have hloop : ∀ i : ℕ, 0 < i → i ≤ 8 →
        Subsingleton (HR (ZMod p) (Path x₀ x₀) i) :=
      fun i hi0 hi8 => Work.Pi6.EMODD.piIsoTransfer (ZMod p) 9
        (Work.Serre.killIncl 9 (Path x₀ x₀))
        (fun j hj x => (Work.Serre.killCells_step 9 (Path x₀ x₀)).1 j (by omega) x)
        (fun j hj0 hj9 => hem j hj0 (by omega)) i hi0 (by omega)
    exact Work.Pi6.EMODD.emOddLoop p hM 3 N (by norm_num) hN X x₀ hX hloop


end Work.Pi6
