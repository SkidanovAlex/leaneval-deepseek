import Mathlib
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLC6Core.atom_gen_cut
import Submission.Work.EKLComp.V_hasBasis_nhds_one
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLC6Core.V_mul_mem_V

/-!
# `Work.EKLC6Core.isOpen_shape_cut_cell`

The shape of the cut σ-algebra at a point of a cell is the trace on `U` of an open subset of
`SL₃(ℝ)` — the openness half of Pisa 7.38 for the cells of `CutData`.

Let `S : CutData μ U ε` be the cut data of `cutSetup.lean` (finitely many disjoint open cells
`cell i` with lifts `lift i` in the ball `V (10 ρ) · (g i)`, unique there) and let
`M = σ(range genCell S O ∪ {bad})` be the cut σ-algebra.  For `y ∈ S.cell i`
`atom_gen_cut` computes the atom

`atom_M y = {w ∈ cell i | ∃ u ∈ U, lift i w = u * lift i y}`.

The task is to show that `shape M U y = {u ∈ U | u • y ∈ atom_M y}` is the trace of an open set.

The argument is the "fat atom" argument (`isOpen_shape_of_fat_atom`), self-contained here: it
suffices to show that for every `z ∈ atom_M y` and every `v ∈ U` close enough to `1` one has
`v • z ∈ atom_M z`.  For such a `z`, `atom_gen_cut` provides `u₀ ∈ U` with
`lift i z = u₀ * lift i y`.  Now choose `δ` so small that

* `v • z ∈ cell i` for `v ∈ V δ` (`cell i` is open and `v ↦ v • z` is continuous), and
* `v * a ∈ V (10 ρ)` whenever `v ∈ V δ` and `a ∈ V (10 ρ)` (`V_mul_mem_V`: the strict
  inequalities in the definition of `V` leave a positive margin).

Then `v * lift i z` maps to `v • z` and still lies in the lift ball `V (10 ρ) · (g i)`, so by the
*uniqueness* of the lift `lift i (v • z) = v * lift i z = (v * u₀) * lift i y` with `v * u₀ ∈ U`,
i.e. `v • z ∈ atom_M y = atom_M z`.  Note that `lift_eq` (local `U`-equivariance, which needs the
freeness of `z`) is *not* used: measuring the perturbation against the lift of `z` itself supplies
the margin that `lift_eq` obtains from freeness at the base point.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open MeasureTheory Topology
open Work.EKLContract

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3} {ε : ℝ}

/-- `V` is monotone in its radius. -/
private lemma V_mono_loc {s t : ℝ} (h : s ≤ t) : V s ⊆ V t :=
  fun g hg i j => lt_of_lt_of_le (hg i j) h

/-- **The orbit map is continuous at the identity.**  If `z` lies in the open set `A`, then every
`v` close enough to `1` in the entrywise sense satisfies `v • z ∈ A`. -/
private lemma exists_V_smul_subset_loc {A : Set X3} (hA : IsOpen A) {z : X3} (hz : z ∈ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : SL3, v ∈ V δ → v • z ∈ A := by
  have hcont : Continuous fun v : SL3 => v • z :=
    (continuous_smul (M := SL3)).comp (continuous_id.prodMk continuous_const)
  have hopen : IsOpen {v : SL3 | v • z ∈ A} := hA.preimage hcont
  have h1 : (1 : SL3) ∈ {v : SL3 | v • z ∈ A} := by simpa using hz
  exact Work.EKLComp.V_hasBasis_nhds_one.mem_iff.mp (hopen.mem_nhds h1)

/-- The right translate of an entry ball: `{g | g * u⁻¹ ∈ V δ}` is open. -/
private lemma isOpen_translate_V_loc (u : SL3) (δ : ℝ) :
    IsOpen {g : SL3 | g * u⁻¹ ∈ V δ} :=
  (isOpen_V δ).preimage (continuous_id.mul continuous_const)

/-- **A fat atom has relatively open shape.**  If for every `z` of the atom `[x]_m` the small
`U`-translates of `z` stay in `[x]_m`, then `shape m U x` is the trace on `U` of an open set of
`SL₃(ℝ)`. -/
private theorem isOpen_shape_of_fat_atom_loc {m : MeasurableSpace X3} {U : Subgroup SL3}
    {x : X3} (hfat : ∀ z ∈ atom m x, ∃ δ : ℝ, 0 < δ ∧ ∀ v : SL3, v ∈ U → v ∈ V δ →
      v • z ∈ atom m x) :
    ∃ O : Set SL3, IsOpen O ∧ shape m U x = O ∩ (U : Set SL3) := by
  classical
  let F : {u : SL3 // u ∈ shape m U x} → ℝ :=
    fun u => Classical.choose (hfat (u.1 • x) u.2.2)
  have hFpos : ∀ u : {u : SL3 // u ∈ shape m U x}, 0 < F u :=
    fun u => (Classical.choose_spec (hfat (u.1 • x) u.2.2)).1
  have hFspec : ∀ u : {u : SL3 // u ∈ shape m U x}, ∀ v : SL3, v ∈ U → v ∈ V (F u) →
      v • (u.1 • x) ∈ atom m x :=
    fun u => (Classical.choose_spec (hfat (u.1 • x) u.2.2)).2
  refine ⟨⋃ u : {u : SL3 // u ∈ shape m U x}, {g : SL3 | g * u.1⁻¹ ∈ V (F u)},
    isOpen_iUnion fun u => isOpen_translate_V_loc u.1 (F u), ?_⟩
  ext w
  constructor
  · rintro ⟨hwU, hwat⟩
    refine ⟨Set.mem_iUnion.mpr ⟨⟨w, hwU, hwat⟩, ?_⟩, hwU⟩
    have h1 : (w * w⁻¹ : SL3) = 1 := mul_inv_cancel w
    have h2 : ∀ i j : Fin 3, |((w * w⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j -
        (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < F ⟨w, hwU, hwat⟩ := by
      intro i j
      rw [h1]
      simpa using hFpos ⟨w, hwU, hwat⟩
    exact h2
  · rintro ⟨hwO, hwU⟩
    rcases Set.mem_iUnion.mp hwO with ⟨u, hu⟩
    have huinv : w * u.1⁻¹ ∈ U := U.mul_mem hwU (U.inv_mem u.2.1)
    have hspec := hFspec u (w * u.1⁻¹) huinv hu
    have hsmul : (w * u.1⁻¹) • (u.1 • x) = w • x := by
      rw [← mul_smul, show (w * u.1⁻¹) * u.1 = w from by group]
    rw [hsmul] at hspec
    exact ⟨hwU, hspec⟩

theorem isOpen_shape_cut_cell {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) (O : ℕ → Set Work.EKLContract.SL3)
    (hOopen : ∀ m, IsOpen (O m))
    (hvis : ∀ z : Work.EKLContract.SL3, ∃ m, z ∈ Work.EKLC6Core.sat U (O m))
    (hsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (z ∈ Work.EKLC6Core.sat U (O m) ↔ w ∈ Work.EKLC6Core.sat U (O m))) →
      w ∈ Work.EKLC6Core.sat U ({z} : Set Work.EKLContract.SL3))
    (i : Fin S.N) (y : Work.EKLContract.X3) (hy : y ∈ S.cell i) :
    ∃ W : Set Work.EKLContract.SL3, IsOpen W ∧
      Work.EKLContract.shape (MeasurableSpace.generateFrom (Set.range
        (fun p : Fin S.N × ℕ => Work.EKLC6Core.genCell S O p.1 p.2) ∪ {S.bad})) U y
        = W ∩ (U : Set Work.EKLContract.SL3) := by
  classical
  set M : MeasurableSpace X3 := MeasurableSpace.generateFrom (Set.range
    (fun p : Fin S.N × ℕ => genCell S O p.1 p.2) ∪ {S.bad}) with hM
  -- the atom of a point of a cell, `EKLC6Core.atom_gen_cut`
  have hatom : atom M y = {w : X3 | w ∈ S.cell i ∧
      ∃ u ∈ (U : Set SL3), S.lift i w = u * S.lift i y} :=
    atom_gen_cut S O hOopen hvis hsep i y hy
  -- the atom is fat: small `U`-perturbations of its points stay inside it
  have hfat : ∀ z ∈ atom M y, ∃ δ : ℝ, 0 < δ ∧ ∀ v : SL3, v ∈ U → v ∈ V δ →
      v • z ∈ atom M y := by
    intro z hz
    have hzA := hatom ▸ hz
    obtain ⟨hzcell, u₀, hu₀U, hlift₀⟩ := hzA
    -- a radius keeping `v • z` inside the (open) cell
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_V_smul_subset_loc (S.hopen i) hzcell
    -- a radius keeping `v * lift i z` inside the lift ball, by the margin in `V (10 ρ)`
    obtain ⟨a₀, ha₀, ha₀eq⟩ := S.lift_bdd i z hzcell
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := V_mul_mem_V (by linarith [S.hρ] : (0 : ℝ) < 10 * S.ρ) ha₀
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun v hvU hvV => ?_⟩
    have hv₁ : v ∈ V δ₁ := V_mono_loc (min_le_left _ _) hvV
    have hv₂ : v ∈ V δ₂ := V_mono_loc (min_le_right _ _) hvV
    have hcell' : v • z ∈ S.cell i := hδ₁ v hv₁
    have hmemB : v * S.lift i z ∈ shift (V (10 * S.ρ)) (S.g i) :=
      ⟨v * a₀, hδ₂ v hv₂, by rw [mul_assoc, ha₀eq]⟩
    have hmk : mkX (v * S.lift i z) = v • z := by
      rw [Work.EKLContract.Lemmas.mkX_mul, S.lift_mk i z hzcell]
    have hunq : v * S.lift i z = S.lift i (v • z) :=
      S.lift_uniq i (v • z) hcell' (v * S.lift i z) hmk hmemB
    have hmemA : v • z ∈ {w : X3 | w ∈ S.cell i ∧
        ∃ u ∈ (U : Set SL3), S.lift i w = u * S.lift i y} :=
      ⟨hcell', v * u₀, U.mul_mem hvU hu₀U, by rw [← hunq, hlift₀, mul_assoc]⟩
    exact hatom.symm ▸ hmemA
  exact isOpen_shape_of_fat_atom_loc hfat

end Work.EKLC6Core
