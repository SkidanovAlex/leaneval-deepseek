import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.pairMeetDefs
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.ppIntrinsic.Defs
import Submission.Work.Drive.ppIntrinsic.PPRegAt_ppShift_of_collarBoundary

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The identity perturbation leaves a chain unchanged. -/
lemma edrc_ppShift_id (w : ℝ → ℝ) (v : EuclideanSpace ℝ (Fin 4))
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → M) : ppShift (fun _ p => p) w v E = E := rfl

/-- **The pair-meet set is closed** (it is a closed subset of the unit box, cut out by two equations
between continuous maps). -/
theorem edrc_isClosed_ppMeet
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    IsClosed (ppMeet E E' V W) := by
  have hftS : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftS z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
    fun_prop
  have hftU : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftU z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 2 => z ⟨1 + i.val, by omega⟩))
    fun_prop
  have hftY : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftY z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨3 + i.val, by omega⟩))
    fun_prop
  have hftZ : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftZ z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨6 + i.val, by omega⟩))
    fun_prop
  have hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)) :=
    hE.continuous.comp (hftS.prodMk hftU)
  have hE'c : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E' (ftS z) (ftU z)) :=
    hE'.continuous.comp (hftS.prodMk hftU)
  have hVc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) :=
    hV.continuous.comp hftY
  have hWc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) :=
    hW.continuous.comp hftZ
  have h1 : IsClosed {z : EuclideanSpace ℝ (Fin 9) | E (ftS z) (ftU z) = V (ftY z)} :=
    isClosed_eq hEc hVc
  have h2 : IsClosed {z : EuclideanSpace ℝ (Fin 9) | E' (ftS z) (ftU z) = W (ftZ z)} :=
    isClosed_eq hE'c hWc
  have h3 : ppMeet E E' V W =
      (Submission.Drive.unitBox 8 ∩
        {z : EuclideanSpace ℝ (Fin 9) | E (ftS z) (ftU z) = V (ftY z)}) ∩
        {z : EuclideanSpace ℝ (Fin 9) | E' (ftS z) (ftU z) = W (ftZ z)} := by
    ext z
    rw [mem_ppMeet]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Submission.Drive.unitBox]
    tauto
  rw [h3]
  exact ((Work.Drive.isClosed_unitBox 8).inter h1).inter h2

/-- **Locality of the pair regularity at a meet**: at a meet where the pair map is regular (both
clauses of `PPRegAt`), every meet in a neighbourhood is regular.  The proof is the one already used
for the collar-boundary transfer: the self-centred regularity at a meet is equivalent to the
regularity of the *fixed-chart* pair map, which is an open condition, and the local form
`ppIntrinsic.ppRegAt_local` (which is precisely this statement in the perturbed-family form,
applied with the identity perturbation) gives the neighbourhood. -/
theorem edrc_local_regular
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {x₀ : EuclideanSpace ℝ (Fin 9)} (hx₀ : x₀ ∈ ppMeet E E' V W)
    (hreg : PPRegAt E E' V W x₀) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 9)), IsOpen U ∧ x₀ ∈ U ∧
      ∀ y ∈ U, y ∈ ppMeet E E' V W → PPRegAt E E' V W y := by
  classical
  have hbasefull : Function.Surjective
      (fderiv ℝ (ppDiff (Work.Drive.ppIntrinsic.pC E x₀) (Work.Drive.ppIntrinsic.pC' E' x₀)
        E E' V W) x₀) := hreg.1
  have main : ∀ (I : Finset (Fin 9)),
      (∀ i ∈ I, Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
        fderiv ℝ (ppDiff (Work.Drive.ppIntrinsic.pC E x₀)
          (Work.Drive.ppIntrinsic.pC' E' x₀) E E' V W) x₀ v.1)) →
      ∀ (ρ : ℝ), 0 < ρ → (∀ y, y ∈ Metric.ball x₀ ρ → y ∈ Submission.Drive.unitBoxBdry 8 →
        ∃ i ∈ I, (y i = 0 ∨ y i = 1) ∧ ∀ j : Fin 9, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) →
      ∃ U, IsOpen U ∧ x₀ ∈ U ∧ ∀ y ∈ U, y ∈ ppMeet E E' V W → PPRegAt E E' V W y := by
    intro I hres ρ hρ hforce
    obtain ⟨ε, hε, U, hUopen, hxU, -, hprop⟩ :=
      Work.Drive.ppIntrinsic.ppRegAt_local (fun _ p => p) (fun p => rfl) contMDiff_snd
        hE hE' hV hW contDiff_const hx₀ hbasefull I hres hρ hforce
    refine ⟨U, hUopen, hxU, fun y hyU hyM => ?_⟩
    have h1 : PPRegAt (ppShift (fun _ p => p) (fun _ => 0)
          (unpackFst (0 : EuclideanSpace ℝ (Fin 8))) E)
        (ppShift (fun _ p => p) (fun _ => 0)
          (unpackSnd (0 : EuclideanSpace ℝ (Fin 8))) E') V W y := by
      refine hprop 0 (by simpa using hε) y hyU ?_
      rw [edrc_ppShift_id, edrc_ppShift_id]
      exact hyM
    rwa [edrc_ppShift_id, edrc_ppShift_id] at h1
  by_cases hb : ∃ i : Fin 9, x₀ i = 0 ∨ x₀ i = 1
  · obtain ⟨i₀, hi₀, hoth₀, hres₀⟩ := hreg.2 ⟨hx₀.1, hb⟩
    have hopen_i : IsOpen {y : EuclideanSpace ℝ (Fin 9) |
        ∀ j : Fin 9, j ≠ i₀ → y j ∈ Set.Ioo (0 : ℝ) 1} := by
      rw [show {y : EuclideanSpace ℝ (Fin 9) | ∀ j : Fin 9, j ≠ i₀ → y j ∈ Set.Ioo (0 : ℝ) 1}
          = ⋂ j ∈ (Finset.univ.erase i₀),
            {y : EuclideanSpace ℝ (Fin 9) | y j ∈ Set.Ioo (0 : ℝ) 1} from by
        ext y; simp [Finset.mem_erase]]
      exact isOpen_biInter_finset fun j _ =>
        isOpen_Ioo.preimage (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 9) => y j)
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hopen_i.mem_nhds hoth₀)
    refine main {i₀} ?_ ρ hρ ?_
    · intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      exact hres₀
    · intro y hy hybdry
      obtain ⟨i, hi⟩ := hybdry.2
      by_cases hii : i = i₀
      · subst hii
        exact ⟨i, Finset.mem_singleton_self i, hi, fun j hj => hρsub hy j hj⟩
      · obtain ⟨h1, h2⟩ := hρsub hy i hii
        rcases hi with h | h
        · exact absurd (h ▸ h1) (lt_irrefl 0)
        · exact absurd (h ▸ h2) (lt_irrefl 1)
  · have hall : ∀ j : Fin 9, x₀ j ∈ Set.Ioo (0 : ℝ) 1 := by
      intro j
      have h1 := hx₀.1 j
      exact ⟨lt_of_le_of_ne h1.1 (fun h => hb ⟨j, Or.inl h.symm⟩),
             lt_of_le_of_ne h1.2 (fun h => hb ⟨j, Or.inr h⟩)⟩
    have hopen_all : IsOpen {y : EuclideanSpace ℝ (Fin 9) |
        ∀ j : Fin 9, y j ∈ Set.Ioo (0 : ℝ) 1} := by
      rw [show {y : EuclideanSpace ℝ (Fin 9) | ∀ j : Fin 9, y j ∈ Set.Ioo (0 : ℝ) 1}
          = ⋂ j ∈ (Finset.univ : Finset (Fin 9)),
            {y : EuclideanSpace ℝ (Fin 9) | y j ∈ Set.Ioo (0 : ℝ) 1} from by
        ext y; simp]
      exact isOpen_biInter_finset fun j _ =>
        isOpen_Ioo.preimage (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 9) => y j)
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hopen_all.mem_nhds hall)
    refine main ∅ (fun i hi => absurd hi (Finset.notMem_empty i)) ρ hρ ?_
    intro y hy hybdry
    exfalso
    obtain ⟨i, hi⟩ := hybdry.2
    obtain ⟨h1, h2⟩ := hρsub hy i
    rcases hi with h | h
    · exact lt_irrefl 0 (h ▸ h1)
    · exact lt_irrefl 1 (h ▸ h2)

end

theorem exists_delta_regular_collar
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hend : ∀ x ∈ Work.Drive.ppMeet E E' V W,
      (Work.Drive.ftS x = 0 ∨ Work.Drive.ftS x = 1) → Work.Drive.PPRegAt E E' V W x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ x ∈ Work.Drive.ppMeet E E' V W,
      (Work.Drive.ftS x ≤ δ ∨ 1 - δ ≤ Work.Drive.ftS x) → Work.Drive.PPRegAt E E' V W x := by
  classical
  by_contra hcon
  have hcon' : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ x ∈ ppMeet E E' V W,
      (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) ∧ ¬ PPRegAt E E' V W x := by
    intro δ hδ hδ2
    by_contra h
    push Not at h
    exact hcon ⟨δ, hδ, hδ2, h⟩
  have hbad : ∀ n : ℕ, ∃ x ∈ ppMeet E E' V W,
      (ftS x ≤ 1 / ((n : ℝ) + 3) ∨ 1 - 1 / ((n : ℝ) + 3) ≤ ftS x) ∧
        ¬ PPRegAt E E' V W x := by
    intro n
    refine hcon' _ (by positivity) ?_
    have h3 : (2 : ℝ) < (n : ℝ) + 3 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact one_div_lt_one_div_of_lt (by norm_num) h3
  choose x hxmem hxcol hxirr using hbad
  have hKcomp : IsCompact (ppMeet E E' V W) :=
    (Work.Drive.isCompact_unitBox 8).of_isClosed_subset
      (edrc_isClosed_ppMeet hE hE' hV hW) (fun z hz => (mem_ppMeet.mp hz).1)
  obtain ⟨x₀, hx₀K, φ, hφmono, hφtend⟩ := hKcomp.tendsto_subseq hxmem
  have hftSc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftS z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
    fun_prop
  have hftT : Tendsto (fun n => ftS (x (φ n))) atTop (𝓝 (ftS x₀)) := by
    have h := (hftSc.tendsto x₀).comp hφtend
    simpa only [Function.comp_def] using h
  have hδT : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  have hbound : ∀ n : ℕ, ftS (x (φ n)) ≤ 1 / ((n : ℝ) + 3) ∨
      1 - 1 / ((n : ℝ) + 3) ≤ ftS (x (φ n)) := by
    intro n
    have hn : n ≤ φ n := hφmono.le_apply
    have hcast : (n : ℝ) + 3 ≤ ((φ n : ℕ) : ℝ) + 3 := by
      have : (n : ℝ) ≤ ((φ n : ℕ) : ℝ) := by exact_mod_cast hn
      linarith
    have h1 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    have hle := one_div_le_one_div_of_le h1 hcast
    rcases hxcol (φ n) with h | h
    · exact Or.inl (le_trans h hle)
    · exact Or.inr (le_trans (by linarith : 1 - 1 / ((n : ℝ) + 3) ≤
          1 - 1 / (((φ n : ℕ) : ℝ) + 3)) h)
  have hlim : ftS x₀ ≤ 0 ∨ 1 ≤ ftS x₀ := by
    by_contra h
    push Not at h
    have hA : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 3) < ftS (x (φ n)) := by
      have hsub : Tendsto (fun n : ℕ => ftS (x (φ n)) - (1 : ℝ) / ((n : ℝ) + 3)) atTop
          (𝓝 (ftS x₀ - 0)) := hftT.sub hδT
      have hpos : (0 : ℝ) < ftS x₀ - 0 := by linarith [h.1]
      filter_upwards [hsub.eventually (Ioi_mem_nhds hpos)] with n hn
      linarith
    have hB : ∀ᶠ n : ℕ in atTop, ftS (x (φ n)) < 1 - (1 : ℝ) / ((n : ℝ) + 3) := by
      have hsub : Tendsto (fun n : ℕ => (1 - (1 : ℝ) / ((n : ℝ) + 3)) - ftS (x (φ n))) atTop
          (𝓝 (1 - ftS x₀)) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - (1 : ℝ) / ((n : ℝ) + 3)) atTop
            (𝓝 ((1 : ℝ) - 0)) := hδT.const_sub 1
        have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) - (1 : ℝ) / ((n : ℝ) + 3)) - ftS (x (φ n)))
            atTop (𝓝 (((1 : ℝ) - 0) - ftS x₀)) := h1.sub hftT
        simpa only [sub_zero] using h2
      have hpos : (0 : ℝ) < 1 - ftS x₀ := by linarith [h.2]
      filter_upwards [hsub.eventually (Ioi_mem_nhds hpos)] with n hn
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hA.and hB)
    obtain ⟨hN1, hN2⟩ := hN N le_rfl
    rcases hbound N with hb | hb <;> linarith
  have hx₀end : ftS x₀ = 0 ∨ ftS x₀ = 1 := by
    have hbox : (0 : ℝ) ≤ ftS x₀ ∧ ftS x₀ ≤ 1 := by
      show (0 : ℝ) ≤ x₀ 0 ∧ x₀ 0 ≤ 1
      exact (mem_ppMeet.mp hx₀K).1 (0 : Fin 9)
    rcases hlim with h | h
    · exact Or.inl (le_antisymm h hbox.1)
    · exact Or.inr (le_antisymm hbox.2 h)
  have hreg₀ : PPRegAt E E' V W x₀ := hend x₀ hx₀K hx₀end
  obtain ⟨U, hUopen, hxU, hUreg⟩ := edrc_local_regular hE hE' hV hW hx₀K hreg₀
  have hev : ∀ᶠ n : ℕ in atTop, x (φ n) ∈ U := by
    filter_upwards [hφtend.eventually (hUopen.mem_nhds hxU)] with n hn
    exact hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact hxirr (φ N) (hUreg (x (φ N)) (hN N le_rfl) (hxmem (φ N)))

end Work.Drive.ppParity
