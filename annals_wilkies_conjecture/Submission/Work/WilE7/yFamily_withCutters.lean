/-
  Area E7 / `CoreLT_succ`: **the `Y`-family with the cutters present** (`yFamily_withCutters`).

  ## What this file delivers

  For every format bound `F` there are constants `A M : ℕ` and polynomials `B Q : ℕ[X]` such that
  for every `Good` absolute stratum `T : Stratum 0 (n+(m+1))` with `T.X.fmt ≤ F` and `T.deg ≤ D`
  there is a *packed* list `Yl : List (SemiPf (n+M))` with `Yl.length ≤ Q.eval D`, every member of
  format `≤ A` and degree `≤ Q.eval D`, together with

  * `L` — the `E5`-strata of the frontier `closure T.X.set \ T.X.set` (the *branch cutters*), of
    length `≤ B.eval D`, format `≤ A`, degree `≤ B.eval D`, each `Good` and contained in the
    frontier, covering the frontier exactly; every cutter `S` is *represented* in `Yl` by a member
    with `projFirst n M '' Y.set = projFirst n (m+1) '' absSet S`;
  * `R` — the refined fibre cut of `T` (members inside `closure (absSet T)` with finite
    `π_n`-fibres), covering `π_n (closure (absSet T))` exactly, every member again represented
    in `Yl` with the same base projection.

  The proof: `frontierFamily_uniform` (below) produces the strata `L` from `hE5` + `hE6`,
  `coreLT_succ.refinedCutFamily` produces the cut `R` from the *proved* components bound
  `Work.WilE2.E2_components_proved` (`E2b`, no `sorry`: its axioms are exactly
  `[propext, Classical.choice, Quot.sound]`), and `yFamily_pack_family` packs the two lists into
  the single list `Yl`, preserving every candidate's base projection.  The dimension `M := F`
  works because `T.X.fmt ≤ F` forces `n + (m+1) ≤ F`, and the bound polynomial is
  `Q := 4 * (B + br + 1)` (`eval` is monotone, coefficients are in `ℕ`).

  ## Repair of the requested statement — read before using

  The statement requested for this path **does not elaborate**, so no declaration of the
  requested shape can exist in any file.  Its third conjunct reads

      ∀ Y ∈ R, Y.set ⊆ closure T.X.set ∧ ...

  but `Y : SemiPf (n + (m + 1))` while `T : Stratum 0 (n + (m + 1))`, hence
  `Y.set : Set (Fin (n+(m+1)) → ℝ)` and `T.X.set : Set (Fin (0 + (n+(m+1))) → ℝ)`.  Lean rejects
  the statement with

      Application type mismatch: The argument
        T.X.set
      has type
        Set (Fin (0 + (n + (m + 1))) → ℝ)
      but is expected to have type
        Set (Fin (n + (m + 1)) → ℝ)
      in the application
        closure T.X.set

  (`0 + (n+(m+1))` is *not* definitionally `n+(m+1)`: `Nat.add` recurses on its second
  argument, so `Nat.zero_add` is a theorem, not `rfl`).

  The set of the absolute stratum `T` is transported to `ℝ^{n+(m+1)}` by `MainDesign.absSet`
  (`absSet T = absPt '' T.X.set`, the image under the value-preserving identification
  `Fin (0+N) ≃ Fin N`), and it is *this* set that the rest of the statement already uses (the
  covering clause is `projFirst n (m+1) '' closure (absSet T) = ⋃ ...`, and the presence clause is
  `... = projFirst n (m+1) '' absSet S` for the cutters).  The least repair — the only one that
  makes the clause typecheck and agree with the other two `absSet` occurrences — is therefore

      ∀ Y ∈ R, Y.set ⊆ closure (Work.WilE7.MainDesign.absSet T) ∧ ...

  which is what the declaration below carries; everything else is verbatim.  Since `absSet T` is
  the homeomorphic transport of `T.X.set` (the two sets have the same closure), the repaired
  statement says exactly what was meant.  The repair is not cosmetic *here*: it is the form that
  `refinedCutFamily`, applied to the reindexed stratum (whose set *is* `absSet T`), delivers.
-/
import Mathlib
import Submission.Work.WilE7.coreLT_succ.frontierFamily
import Submission.Work.WilE7.coreLT_succ.refinedCutFamily
import Submission.Work.WilE7.yFamily_pack_family
import Submission.Work.WilE7.E6closure
import Submission.Work.WilE2.E2_components_proved

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## The transport `Fin (0 + N) ≃ Fin N` versus `MainDesign.absPt` -/

/-- A semi-Pfaffian set in `ℝ^{0+N}`, reindexed along the value-preserving identification
`Fin (0+N) ≃ Fin N`, has as its set exactly the transport `absPt '' X.set` that
`MainDesign.absSet` uses for the absolute strata (both descriptions are "forget the empty block
of coordinates"). -/
theorem reindex_zero_absPt {N : ℕ} (X : WilkiesDesign.E.SemiPf (0 + N)) :
    (Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv (Nat.zero_add N)) X).set =
      Work.WilE7.MainDesign.absPt '' X.set := by
  ext y
  rw [Work.WilE7.sp_reindex_mem]
  constructor
  · -- `y` lies in the reindexed set: then `y = absPt (y ∘ e)`
    intro hz
    refine ⟨fun i => y (Work.WilE7.finEquiv (Nat.zero_add N) i), hz, ?_⟩
    funext j
    rfl
  · -- `y = absPt z` with `z ∈ X.set`: then `y ∘ e = z`
    rintro ⟨z, hz, rfl⟩
    have hfun : (fun i => Work.WilE7.MainDesign.absPt z
        (Work.WilE7.finEquiv (Nat.zero_add N) i)) = z := by
      funext i
      rfl
    rw [hfun]
    exact hz

/-! ## The frontier family with constants uniform in `n`, `m` -/

/-- The frontier family of `coreLT_succ.frontierFamily`, with the constants *uniform* in the
ambient dimensions `n`, `m` (in the proof below they are already independent of them, but the
original statement takes `n`, `m` before `F`, so its existential quantifiers sit inside them).
A consumer needs the uniform form, since the constants `A`, `B` of `yFamily_withCutters` may not
depend on `n`, `m` or `D`. -/
theorem frontierFamily_uniform
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m D : ℕ) (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))),
        T.Good → T.X.fmt ≤ F → T.deg ≤ D →
        ∃ L : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
          (∀ S ∈ L, S.Good) ∧
          (∀ S ∈ L, S.X.fmt ≤ A ∧ S.deg ≤ B.eval D) ∧
          (∀ S ∈ L, S.X.set ⊆ closure T.X.set \ T.X.set) ∧
          ((closure T.X.set \ T.X.set) ⊆ ⋃ S ∈ L, S.X.set) ∧
          L.length ≤ B.eval D := by
  -- `E6` and `E5` at the format thresholds at which they are used (all constants `F`-only).
  obtain ⟨a₆, b₆, hE6'⟩ := hE6 F
  obtain ⟨a₅, b₅, hE5'⟩ := hE5 a₆
  refine ⟨a₅, b₅.comp b₆, ?_⟩
  intro n m D T _hT hF hD
  have hXd : T.X.deg ≤ D := le_trans (Nat.le_add_right _ _) hD
  -- the ambient frontier of `T` is the `Y'` produced by `E6` over the trivial base
  obtain ⟨Y, Y', _hYfmt, _hYdeg, hY'fmt, hY'deg, _hYset, hY'set⟩ :=
    hE6' 0 (n + (m + 1)) T.X hF
  have hfc : WilkiesDesign.E.fiberClosure T.X.set = closure T.X.set :=
    Work.WilE7.MainDesign.fiberClosure_zero T.X.set
  have hY' : Y'.set = closure T.X.set \ T.X.set := by rw [hY'set, hfc]
  have hY'degD : Y'.deg ≤ b₆.eval D :=
    le_trans hY'deg (Work.WilE7.coreLT_succ.eval_mono_nat b₆ hXd)
  -- stratify that frontier (`E5` over the trivial base, `p = 0`)
  obtain ⟨L, hLlen, hLprops, hLcov, _hLdisj⟩ := hE5' 0 (n + (m + 1)) Y' hY'fmt
  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    exact (hLprops S hS).2.2
  · intro S hS
    refine ⟨(hLprops S hS).1, ?_⟩
    calc S.deg ≤ b₅.eval Y'.deg := (hLprops S hS).2.1
      _ ≤ b₅.eval (b₆.eval D) := Work.WilE7.coreLT_succ.eval_mono_nat b₅ hY'degD
      _ = (b₅.comp b₆).eval D := by rw [Polynomial.eval_comp]
  · intro S hS z hz
    have h1 : z ∈ Y'.set := by
      rw [hLcov]
      exact Set.mem_iUnion₂.mpr ⟨S, hS, hz⟩
    rwa [hY'] at h1
  · intro z hz
    have h1 : z ∈ Y'.set := by rwa [hY']
    rwa [← hLcov]
  · calc L.length ≤ b₅.eval Y'.deg := hLlen
      _ ≤ b₅.eval (b₆.eval D) := Work.WilE7.coreLT_succ.eval_mono_nat b₅ hY'degD
      _ = (b₅.comp b₆).eval D := by rw [Polynomial.eval_comp]

/-! ## The main statement -/

theorem yFamily_withCutters
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (F : ℕ) :
    ∃ (A M : ℕ) (B Q : Polynomial ℕ),
      ∀ (n m D : ℕ) (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))),
        T.Good → T.X.fmt ≤ F → T.deg ≤ D →
        ∃ (Yl : List (WilkiesDesign.E.SemiPf (n + M))),
          Yl.length ≤ Q.eval D ∧
          (∀ Y ∈ Yl, Y.fmt ≤ A ∧ Y.deg ≤ Q.eval D) ∧
          (∃ (L : List (WilkiesDesign.E.Stratum 0 (n + (m + 1)))),
            (∀ S ∈ L, S.X.fmt ≤ A ∧ S.deg ≤ B.eval D ∧ S.Good ∧
              S.X.set ⊆ closure T.X.set \ T.X.set) ∧
            L.length ≤ B.eval D ∧
            (closure T.X.set \ T.X.set = ⋃ S ∈ L, S.X.set) ∧
            (∀ S ∈ L, ∃ Y ∈ Yl,
              WilkiesDesign.E.projFirst n M '' Y.set =
                WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S)) ∧
          (∃ (R : List (WilkiesDesign.E.SemiPf (n + (m + 1)))),
            (∀ Y ∈ R, Y.set ⊆ closure (Work.WilE7.MainDesign.absSet T) ∧
              (∀ x, (WilkiesDesign.E.fiber Y.set x).Finite) ∧
              Y.fmt ≤ A ∧ Y.deg ≤ Q.eval D) ∧
            (WilkiesDesign.E.projFirst n (m + 1) '' closure (Work.WilE7.MainDesign.absSet T) =
              ⋃ Y ∈ R, WilkiesDesign.E.projFirst n (m + 1) '' Y.set) ∧
            (∀ Y ∈ R, ∃ Y' ∈ Yl,
              WilkiesDesign.E.projFirst n M '' Y'.set =
                WilkiesDesign.E.projFirst n (m + 1) '' Y.set)) := by
  classical
  -- (0) the components bound `E2b`, *proved* in this workspace (WilE2), not assumed here.
  have hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F → ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧
        (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y :=
    Work.WilE2.E2_components_proved
  -- (1) the two producers, with constants depending on `F` only
  obtain ⟨aL, BL, hFam⟩ := frontierFamily_uniform hE5 hE6 F
  obtain ⟨ar, br, hCut⟩ := Work.WilE7.coreLT_succ.refinedCutFamily hE2 hE5 hE6 F
  -- (2) the constants; `M := F` bounds every fibre dimension because `T.X.fmt ≤ F`
  refine ⟨max aL ar + F, F, BL, 4 * (BL + br + 1), ?_⟩
  intro n m D T hT hFmt hDeg
  -- `n + (m+1) ≤ F`, hence `m + 1 ≤ M = F`
  have hdim : m + 1 ≤ F := by
    have h := hFmt
    rw [WilkiesDesign.E.SemiPf.fmt] at h
    omega
  -- the transport `Fin (0 + (n+(m+1))) ≃ Fin (n+(m+1))` and the transported stratum
  let e : Fin (0 + (n + (m + 1))) ≃ Fin (n + (m + 1)) :=
    Work.WilE7.finEquiv (Nat.zero_add (n + (m + 1)))
  have hsetT : (Work.WilE7.SemiPf.reindex e T.X).set = Work.WilE7.MainDesign.absSet T :=
    reindex_zero_absPt T.X
  have hfmtT : (Work.WilE7.SemiPf.reindex e T.X).fmt ≤ F := by
    have h := hFmt
    rw [WilkiesDesign.E.SemiPf.fmt] at h
    show (n + (m + 1)) + T.X.r ≤ F
    omega
  -- (3) the frontier strata of `T` (`E5` + `E6`)
  obtain ⟨L, hLgood, hLprops, hLsub, hLcov, hLlen⟩ := hFam n m D T hT hFmt hDeg
  -- (4) the refined fibre cut of the transported stratum
  obtain ⟨R, hRlen, hRprops, hRcov⟩ := hCut n m (Work.WilE7.SemiPf.reindex e T.X) hfmtT
  -- (5) polynomial bookkeeping: `Q := 4 * (BL + br + 1)` dominates both degree bounds and the
  --     aggregated length bound
  have hQeval : (4 * (BL + br + 1)).eval D = 4 * (BL.eval D + br.eval D + 1) := by
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
  have hdegT : T.X.deg ≤ D := le_trans (Nat.le_add_right _ _) hDeg
  have hbrD : br.eval (Work.WilE7.SemiPf.reindex e T.X).deg ≤ br.eval D :=
    Work.WilE7.coreLT_succ.eval_mono_nat br (by rw [Work.WilE7.sp_reindex_deg]; exact hdegT)
  have hBLe : BL.eval D ≤ (4 * (BL + br + 1)).eval D := by rw [hQeval]; omega
  have hbre : br.eval D ≤ (4 * (BL + br + 1)).eval D := by rw [hQeval]; omega
  -- (6) the candidate family: the reindexed cutters (fibre dimension `m+1`) and the cut `R`
  let Cs : (i : Fin 1) → List (WilkiesDesign.E.SemiPf (n + (m + 1))) :=
    fun _ => (L.map (fun S => Work.WilE7.SemiPf.reindex e S.X)) ++ R
  have hCs : Cs 0 = (L.map (fun S => Work.WilE7.SemiPf.reindex e S.X)) ++ R := rfl
  -- (7) pack the candidates into one list in the common fibre dimension `M = F`
  obtain ⟨Yl, hYllen, hYlprops, hYlpres⟩ :=
    Work.WilE7.yFamily_pack_family (n := n) (m := fun _ : Fin 1 => m + 1) (M := F)
      (fun _ => hdim) Cs (max aL ar)
      (fun _ Y hY => by
        rw [hCs] at hY
        rw [List.mem_append] at hY
        rcases hY with hY | hY
        · rw [List.mem_map] at hY
          obtain ⟨S, hS, rfl⟩ := hY
          refine le_trans ?_ (le_max_left aL ar)
          show (n + (m + 1)) + S.X.r ≤ aL
          have h := (hLprops S hS).1
          rw [WilkiesDesign.E.SemiPf.fmt] at h
          omega
        · exact le_trans (hRprops Y hY).1 (le_max_right aL ar))
      D (4 * (BL + br + 1))
      (fun _ Y hY => by
        rw [hCs] at hY
        rw [List.mem_append] at hY
        rcases hY with hY | hY
        · rw [List.mem_map] at hY
          obtain ⟨S, hS, rfl⟩ := hY
          calc (Work.WilE7.SemiPf.reindex e S.X).deg = S.X.deg := Work.WilE7.sp_reindex_deg e S.X
            _ ≤ S.deg := Nat.le_add_right _ _
            _ ≤ BL.eval D := (hLprops S hS).2
            _ ≤ (4 * (BL + br + 1)).eval D := hBLe
        · calc Y.deg ≤ br.eval (Work.WilE7.SemiPf.reindex e T.X).deg := (hRprops Y hY).2.1
            _ ≤ br.eval D := hbrD
            _ ≤ (4 * (BL + br + 1)).eval D := hbre)
      (BL.eval D + br.eval D)
      (fun _ => by
        rw [hCs, List.length_append, List.length_map]
        exact Nat.add_le_add hLlen (le_trans hRlen hbrD))
  refine ⟨Yl, ?_, hYlprops, ⟨L, ?_, hLlen, ?_, ?_⟩, ⟨R, ?_, ?_, ?_⟩⟩
  · -- length of the packed list
    have h1 : Yl.length ≤ 1 * (BL.eval D + br.eval D) := hYllen
    rw [one_mul] at h1
    refine le_trans h1 ?_
    rw [hQeval]
    omega
  · -- the strata carry the claimed bounds
    intro S hS
    exact ⟨le_trans (hLprops S hS).1
        (le_trans (le_max_left aL ar) (Nat.le_add_right _ F)),
      (hLprops S hS).2, hLgood S hS, hLsub S hS⟩
  · -- they cover the frontier exactly
    exact Set.Subset.antisymm hLcov (fun z hz => by
      obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.mp hz
      exact hLsub S hS hzS)
  · -- every cutter is represented in `Yl`
    intro S hS
    obtain ⟨Y, hY, -, hproj⟩ := hYlpres 0 (Work.WilE7.SemiPf.reindex e S.X)
      (by
        rw [hCs]
        exact List.mem_append_left _ (List.mem_map_of_mem hS))
    refine ⟨Y, hY, ?_⟩
    rw [hproj, reindex_zero_absPt S.X, Work.WilE7.MainDesign.absSet]
  · -- the refined cut: containment, fibre finiteness, format and degree
    intro Y hY
    obtain ⟨hfmtY, hdegY, hsubY, hfinY⟩ := hRprops Y hY
    refine ⟨?_, hfinY, ?_, ?_⟩
    · rw [← hsetT]
      exact hsubY
    · exact le_trans hfmtY
        (le_trans (le_max_right aL ar) (Nat.le_add_right _ F))
    · calc Y.deg ≤ br.eval (Work.WilE7.SemiPf.reindex e T.X).deg := hdegY
        _ ≤ br.eval D := hbrD
        _ ≤ (4 * (BL + br + 1)).eval D := hbre
  · -- it covers `π_n (closure (absSet T))`
    rw [← hsetT]
    exact hRcov
  · -- every member of the cut is represented in `Yl`
    intro Y hY
    obtain ⟨Y', hY', -, hproj⟩ := hYlpres 0 Y
      (by
        rw [hCs]
        exact List.mem_append_right _ hY)
    exact ⟨Y', hY', hproj⟩

end Work.WilE7
