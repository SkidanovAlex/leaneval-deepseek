import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.Drive.EpsForm.discAttach_infra
import Submission.Work.Drive.EpsForm.cluster_cover
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.PinchLemma3.ClosedDiscA.wall_core
import Submission.Work.Smooth.Morse.Flow.exists_continuous_addCircle_lift
import Submission.Work.Drive.EpsForm.exists_continuous_retraction_DiscRegion
import Submission.Work.Drive.EpsForm.exists_path_homotopy_in_discRegion
import Submission.Work.Drive.EpsForm.exists_glued_family
import Submission.Work.Drive.EpsForm.interval_dichotomy_of_not_mem_frontier

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Elementary facts -/

/-- A frontier point of `γ ⁻¹' B` maps into `closure B ∖ B`. -/
theorem frontier_preimage_mem {γ : Work.CoreTopology.ClosedCurve P} {B : Set R3}
    (hSopen : IsOpen (γ ⁻¹' B)) {t : ℝ} (ht : t ∈ frontier (γ ⁻¹' B)) :
    γ t ∈ closure B ∧ γ t ∉ B := by
  refine ⟨?_, ?_⟩
  · have h1 : γ t ∈ γ '' closure (γ ⁻¹' B) := ⟨t, ht.1, rfl⟩
    have h2 := image_closure_subset_closure_image γ.cont h1
    exact closure_mono (by rintro x ⟨s, hs, rfl⟩; exact hs) h2
  · intro hB
    exact ht.2 (by rw [hSopen.interior_eq]; exact hB)

/-- The constant curve has vanishing winding vector. -/
theorem windingOf_constCurve (x : R3) (hx : x ∈ P.carrier) :
    Work.SurgeryInvariance.windingOf P (Work.InnermostDisk.constCurve P x hx) = 0 := by
  by_contra h
  exact Work.InnermostDisk.not_isEssential_of_const P x hx
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P _).mpr h)

/-- An open-in-carrier subset of a proper disc region cannot be the whole carrier: the
carrier contains an essential loop, whereas a loop of an embedded disc is inessential. -/
theorem not_carrier_subset_discRegion (D : Work.SurgeryInvariance.DiscRegion P) :
    ¬ (P.carrier ⊆ D.carrier) := by
  intro hsub
  exact Work.SurgeryInvariance.DiscRegion.not_isEssential D
    (Work.CoreTopology.meridianCurve P 0)
    (fun t => hsub ((Work.CoreTopology.meridianCurve P 0).mem t))
    (Work.CoreTopology.meridianCurve_essential P 0)

/-! ## The main construction

Replacing the excursions of a closed curve into `B` (which lies in the embedded disc `D`) by
paths of `A ∩ D.carrier` joining their endpoints, clustered so that the accumulation points are
handled by a single replacement each. -/

theorem exists_curve_homotopic_into_A {A B : Set R3} {D : Work.SurgeryInvariance.DiscRegion P}
    (hB : B ⊆ D.carrier) (hBopen : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hcl : ∀ x : R3, x ∈ P.carrier → x ∈ closure B → x ∉ B → x ∈ A)
    (hconn : ∀ p : R3, p ∈ closure B → p ∉ B → ∀ q : R3, q ∈ closure B → q ∉ B →
      JoinedIn (A ∩ D.carrier) p q)
    (γ : Work.CoreTopology.ClosedCurve P) (hγAB : ∀ t : ℝ, γ t ∈ A ∪ B)
    (hγ0 : γ 0 ∈ closure B ∧ γ 0 ∉ B) :
    ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ A) ∧
      Work.CoreTopology.Homotopic P γ γ' := by
  classical
  -- ## Step 0: elementary facts
  have hSopen : IsOpen (γ ⁻¹' B) := by
    have hcont : Continuous fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier) :=
      γ.cont.subtype_mk γ.mem
    exact hBopen.preimage hcont
  have hclB : closure B ⊆ D.carrier :=
    closure_minimal hB (Work.PinchLemma3.ClosedDiscA.isClosed_carrier_of_discRegion D)
  -- ## Step 1: a thickening of the disc, and an open set `W` containing the frontier points
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : Work.SurgeryInvariance.DiscRegion P, D.carrier ⊆ D₂.interior :=
    exists_thickening D
  have hD₂carrier : D.carrier ⊆ D₂.carrier := fun x hx => D₂.interior_subset_carrier (hD₂ hx)
  obtain ⟨Φ, hΦ⟩ := exists_continuous_retraction_DiscRegion D₂
  obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp D₂.open_interior
  have hWiff : ∀ x : R3, x ∈ P.carrier → (x ∈ W ↔ x ∈ D₂.interior) := by
    intro x hx
    have h := Set.ext_iff.mp hWeq ⟨x, hx⟩
    exact h
  have hγW : ∀ t : ℝ, t ∈ frontier (γ ⁻¹' B) → γ t ∈ W := by
    intro t ht
    obtain ⟨h1, h2⟩ := frontier_preimage_mem hSopen ht
    exact (hWiff (γ t) (γ.mem t)).mpr (hD₂ (hclB h1))
  -- ## Step 2: the cluster cover of the frontier
  obtain ⟨N, a, b, hab, himg, hdisj, hcov⟩ :=
    exists_disjoint_interval_cover
      (isCompact_Icc.inter_left (isClosed_frontier :
        IsClosed (frontier (γ ⁻¹' B) : Set ℝ)))
      (hWopen.preimage γ.cont) (fun t ht => hγW t ht.1)
  -- ## Step 3: the sorted cut points
  set E : Finset ℝ := insert 0 (insert (2 * Real.pi)
    (Finset.univ.image a ∪ Finset.univ.image b)) with hEdef
  have hEsub : ∀ x ∈ E, x ∈ Set.Icc 0 (2 * Real.pi) := by
    intro x hx
    rw [hEdef] at hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    rcases hx with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨le_rfl, by positivity⟩
    · exact ⟨by positivity, le_rfl⟩
    · exact (hab i).1.2
    · exact (hab i).2.1.2
  have hE0 : (0 : ℝ) ∈ E := by rw [hEdef]; simp
  have hE2 : (2 * Real.pi) ∈ E := by rw [hEdef]; simp
  have hEcard : 1 ≤ E.card := Finset.card_pos.mpr ⟨0, hE0⟩
  set M : ℕ := E.card - 1 with hMdef
  have hcardEq : E.card = M + 1 := by rw [hMdef]; omega
  let u : Fin (M + 1) → ℝ := ⇑(E.orderEmbOfFin hcardEq)
  have hu_strict : StrictMono u := (E.orderEmbOfFin hcardEq).strictMono
  have hu_mem : ∀ j : Fin (M + 1), u j ∈ E := fun j => Finset.orderEmbOfFin_mem E hcardEq j
  have hu_range : Set.range u = ↑E := Finset.range_orderEmbOfFin E hcardEq
  have hminE : ∀ x ∈ E, (0 : ℝ) ≤ x := fun x hx => (hEsub x hx).1
  have hmaxE : ∀ x ∈ E, x ≤ 2 * Real.pi := fun x hx => (hEsub x hx).2
  have hu0 : u 0 = 0 := by
    obtain ⟨j, hj⟩ := show (0 : ℝ) ∈ Set.range u by rw [hu_range]; exact hE0
    have h1 : u 0 ≤ u j := hu_strict.monotone (by simp)
    have h2 : (0 : ℝ) ≤ u 0 := hminE (u 0) (hu_mem 0)
    rw [hj] at h1
    linarith
  have huM : u (Fin.last M) = 2 * Real.pi := by
    obtain ⟨j, hj⟩ := show (2 * Real.pi) ∈ Set.range u by rw [hu_range]; exact hE2
    have h1 : u j ≤ u (Fin.last M) := hu_strict.monotone (Fin.le_last j)
    have h2 : u (Fin.last M) ≤ 2 * Real.pi := hmaxE _ (hu_mem _)
    rw [hj] at h1
    linarith
  have hMpos : 0 < M := by
    by_contra h
    have hM0 : M = 0 := Nat.eq_zero_of_not_pos h
    have hEq : u 0 = u (Fin.last M) := by
      rw [show (0 : Fin (M + 1)) = Fin.last M from Fin.ext (by simp [hM0])]
    rw [hu0, huM] at hEq
    exact absurd hEq (ne_of_lt (by positivity : (0 : ℝ) < 2 * Real.pi))
  -- ## Step 4: the points of `E` are "good" (their `γ`-images lie in `closure B ∖ B`)
  have hgood_cut : ∀ j : Fin (M + 1), γ (u j) ∈ closure B ∧ γ (u j) ∉ B := by
    intro j
    have hmem := hu_mem j
    rw [hEdef] at hmem
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hmem
    rcases hmem with h | h | ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [h]; exact hγ0
    · have hp : γ (2 * Real.pi) = γ 0 := by
        simpa using (γ.periodic 0 : γ (0 + 2 * Real.pi) = γ 0)
      rw [h, hp]
      exact hγ0
    · rw [← hi]
      exact frontier_preimage_mem hSopen (hab i).1.1
    · rw [← hi]
      exact frontier_preimage_mem hSopen (hab i).2.1.1

  -- ## Step 5: every point of `[0,2π]` lies in a piece
  have hpiece_cover : ∀ t : ℝ, t ∈ Set.Icc 0 (2 * Real.pi) →
      ∃ k : Fin M, t ∈ Set.Icc (u k.castSucc) (u k.succ) := by
    intro t ht
    have ht2 : t ≤ u (Fin.last M) := by rw [huM]; exact ht.2
    have hne : (Finset.univ.filter (fun j : Fin (M + 1) => u j ≤ t)).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hu0]; exact ht.1
    set j := (Finset.univ.filter (fun j : Fin (M + 1) => u j ≤ t)).max' hne with hjdef
    have hjle : u j ≤ t := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hjmax : ∀ i : Fin (M + 1), u i ≤ t → i ≤ j := fun i hi =>
      Finset.le_max' _ i (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi)
    rcases eq_or_ne j (Fin.last M) with hlast | hne_last
    · refine ⟨⟨M - 1, by omega⟩, ?_, ?_⟩
      · refine le_trans (hu_strict.monotone ?_) hjle
        rw [hlast, Fin.le_def]
        simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_last]
        omega
      · have hsucc : (⟨M - 1, by omega⟩ : Fin M).succ = Fin.last M :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [hsucc]
        exact ht2
    · have hjval : j.val < M := by
        rcases lt_or_eq_of_le (Fin.le_last j) with h | h
        · simpa [Fin.lt_def] using h
        · exact absurd h hne_last
      refine ⟨Fin.castLT j hjval, ?_, ?_⟩
      · have hcast : (Fin.castLT j hjval).castSucc = j := Fin.ext rfl
        rw [hcast]; exact hjle
      · have hsucc : (Fin.castLT j hjval).succ = ⟨j.val + 1, by omega⟩ := Fin.ext rfl
        rw [hsucc]
        by_contra hcon
        push_neg at hcon
        have hle := hjmax ⟨j.val + 1, by omega⟩ (le_of_lt hcon)
        simp only [Fin.le_def] at hle
        omega
  -- ## Step 6: every piece is either inside a cluster or in a gap
  have hpiece_dich : ∀ k : Fin M,
      (∃ i : Fin N, Set.Icc (u k.castSucc) (u k.succ) ⊆ Set.Icc (a i) (b i)) ∨
      (∀ t : ℝ, t ∈ Set.Ioo (u k.castSucc) (u k.succ) →
        ∀ i : Fin N, t ∉ Set.Icc (a i) (b i)) := by
    intro k
    by_cases hex : ∃ i : Fin N, ∃ t : ℝ,
        t ∈ Set.Ioo (u k.castSucc) (u k.succ) ∧ t ∈ Set.Icc (a i) (b i)
    · left
      obtain ⟨i, t, ht, hti⟩ := hex
      have haE : a i ∈ E := by rw [hEdef]; simp
      have hbE : b i ∈ E := by rw [hEdef]; simp
      obtain ⟨ja, hja⟩ := show a i ∈ Set.range u by rw [hu_range]; exact haE
      obtain ⟨jb, hjb⟩ := show b i ∈ Set.range u by rw [hu_range]; exact hbE
      have hai : a i ≤ u k.castSucc := by
        by_contra hcon
        push_neg at hcon
        have h1 : k.castSucc < ja := by
          rw [← hu_strict.lt_iff_lt, hja]
          exact hcon
        have h2 : ja < k.succ := by
          rw [← hu_strict.lt_iff_lt, hja]
          exact lt_of_le_of_lt hti.1 ht.2
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2
        omega
      have hbi : u k.succ ≤ b i := by
        by_contra hcon
        push_neg at hcon
        have h1 : jb < k.succ := by
          rw [← hu_strict.lt_iff_lt, hjb]
          exact hcon
        have h2 : k.castSucc < jb := by
          rw [← hu_strict.lt_iff_lt, hjb]
          exact lt_of_lt_of_le ht.1 hti.2
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2
        omega
      refine ⟨i, fun z hz => ⟨le_trans hai hz.1, le_trans hz.2 hbi⟩⟩
    · right
      intro t ht i hti
      exact hex ⟨i, t, ht, hti⟩
  -- ## Step 7: on a piece which is not already in `A`, the curve stays in the disc `D₂`
  have hnotkeepD : ∀ k : Fin M,
      ¬ (∀ t : ℝ, t ∈ Set.Icc (u k.castSucc) (u k.succ) → γ t ∈ A) →
      ∀ t : ℝ, t ∈ Set.Icc (u k.castSucc) (u k.succ) → γ t ∈ D₂.carrier := by
    intro k hkeep t ht
    push_neg at hkeep
    obtain ⟨t₀, ht₀mem, ht₀A⟩ := hkeep
    have ht₀B : γ t₀ ∈ B := by
      rcases hγAB t₀ with h | h
      · exact absurd h ht₀A
      · exact h
    rcases hpiece_dich k with ⟨i, hi⟩ | hgap
    · -- a cluster piece
      exact D₂.interior_subset_carrier ((hWiff (γ t) (γ.mem t)).mp (himg i (hi ht)))
    · -- a gap piece
      have ht₀Ioo : t₀ ∈ Set.Ioo (u k.castSucc) (u k.succ) := by
        rcases ht₀mem with ⟨h1, h2⟩
        refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩
        · intro heq
          exact (hgood_cut k.castSucc).2 (heq ▸ ht₀B)
        · intro heq
          exact (hgood_cut k.succ).2 (heq ▸ ht₀B)
      have hfront : ∀ s : ℝ, s ∈ Set.Ioo (u k.castSucc) (u k.succ) →
          s ∉ frontier (γ ⁻¹' B) := by
        intro s hs hfr
        have hsIcc : s ∈ Set.Icc 0 (2 * Real.pi) := by
          refine ⟨?_, ?_⟩
          · rw [← hu0]
            exact le_trans (hu_strict.monotone (by simp [Fin.le_def])) hs.1.le
          · rw [← huM]
            exact le_trans hs.2.le (hu_strict.monotone (Fin.le_last _))
        obtain ⟨i, hi⟩ := hcov s ⟨hfr, hsIcc⟩
        exact hgap s hs i hi
      rcases interval_dichotomy_of_not_mem_frontier hSopen hfront with hBcase | hAcase
      · rcases eq_or_lt_of_le ht.1 with heq | hlt
        · rw [← heq]
          exact hD₂carrier (hclB (hgood_cut k.castSucc).1)
        · rcases eq_or_lt_of_le ht.2 with heq | hlt2
          · rw [heq]
            exact hD₂carrier (hclB (hgood_cut k.succ).1)
          · exact hD₂carrier (hB (hBcase t ⟨hlt, hlt2⟩))
      · exact absurd ht₀B (hAcase t₀ ht₀Ioo)

  -- ## Step 8: the pieces of the family, and the gluing
  have piece_data : ∀ k : Fin M, ∃ Q : ℝ → ℝ → R3,
      Continuous (Function.uncurry Q) ∧
      (∀ s : ℝ, Q s (u k.castSucc) = γ (u k.castSucc) ∧ Q s (u k.succ) = γ (u k.succ)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (u k.castSucc) (u k.succ) →
        Q 0 t = γ t ∧ Q 1 t ∈ A ∧ ∀ s : ℝ, Q s t ∈ P.carrier) := by
    intro k
    by_cases hkeep : ∀ t : ℝ, t ∈ Set.Icc (u k.castSucc) (u k.succ) → γ t ∈ A
    · exact ⟨fun _ t => γ t, γ.cont.comp continuous_snd, fun s => ⟨rfl, rfl⟩,
        fun t ht => ⟨rfl, hkeep t ht, fun s => γ.mem t⟩⟩
    · have huv : u k.castSucc ≤ u k.succ := (hu_strict (Fin.castSucc_lt_succ : k.castSucc < k.succ)).le
      have hjoin : JoinedIn (A ∩ D.carrier) (γ (u k.castSucc)) (γ (u k.succ)) :=
        hconn _ (hgood_cut k.castSucc).1 (hgood_cut k.castSucc).2 _
          (hgood_cut k.succ).1 (hgood_cut k.succ).2
      have hD : ∀ t : ℝ, t ∈ Set.Icc (u k.castSucc) (u k.succ) → γ t ∈ D₂.carrier :=
        hnotkeepD k hkeep
      have hlt : u k.castSucc < u k.succ := hu_strict (Fin.castSucc_lt_succ : k.castSucc < k.succ)
      let cp : ℝ → R3 := fun t => hjoin.somePath (Set.projIcc (0 : ℝ) 1 zero_le_one
        ((t - u k.castSucc) / (u k.succ - u k.castSucc)))
      let br : ℝ → R3 := fun t =>
        if t ∈ Set.Icc (u k.castSucc) (u k.succ) then cp t else γ t
      have hcpcont : Continuous cp :=
        hjoin.somePath.continuous.comp (continuous_projIcc.comp
          ((continuous_id.sub continuous_const).div_const (u k.succ - u k.castSucc)))
      have hcp_a : cp (u k.castSucc) = γ (u k.castSucc) := by
        show hjoin.somePath (Set.projIcc (0 : ℝ) 1 zero_le_one
          ((u k.castSucc - u k.castSucc) / (u k.succ - u k.castSucc))) = γ (u k.castSucc)
        rw [sub_self, zero_div,
          Set.projIcc_of_mem zero_le_one (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
        exact hjoin.somePath.source
      have hcp_b : cp (u k.succ) = γ (u k.succ) := by
        show hjoin.somePath (Set.projIcc (0 : ℝ) 1 zero_le_one
          ((u k.succ - u k.castSucc) / (u k.succ - u k.castSucc))) = γ (u k.succ)
        rw [div_self (by linarith : u k.succ - u k.castSucc ≠ 0),
          Set.projIcc_of_mem zero_le_one (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)]
        exact hjoin.somePath.target
      have hbrcont : Continuous br := by
        show Continuous fun t : ℝ =>
          if t ∈ Set.Icc (u k.castSucc) (u k.succ) then cp t else γ t
        refine continuous_if (p := fun t : ℝ => t ∈ Set.Icc (u k.castSucc) (u k.succ)) ?_
          hcpcont.continuousOn γ.cont.continuousOn
        intro t ht
        have hmem : t ∈ ({u k.castSucc, u k.succ} : Set ℝ) := by
          rw [← frontier_Icc huv]; exact ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl
        · exact hcp_a
        · exact hcp_b
      have hbr_a : br (u k.castSucc) = γ (u k.castSucc) := by
        show (if u k.castSucc ∈ Set.Icc (u k.castSucc) (u k.succ) then cp (u k.castSucc)
          else γ (u k.castSucc)) = γ (u k.castSucc)
        rw [if_pos ⟨le_rfl, huv⟩]
        exact hcp_a
      have hbr_b : br (u k.succ) = γ (u k.succ) := by
        show (if u k.succ ∈ Set.Icc (u k.castSucc) (u k.succ) then cp (u k.succ)
          else γ (u k.succ)) = γ (u k.succ)
        rw [if_pos ⟨huv, le_rfl⟩]
        exact hcp_b
      have hbr_mem : ∀ t : ℝ, t ∈ Set.Icc (u k.castSucc) (u k.succ) → br t ∈ D.carrier := by
        intro t ht
        show (if t ∈ Set.Icc (u k.castSucc) (u k.succ) then cp t else γ t) ∈ D.carrier
        rw [if_pos ht]
        exact (hjoin.somePath_mem _).2
      have hbr_out : ∀ t : ℝ, t ∉ Set.Icc (u k.castSucc) (u k.succ) → br t = γ t := by
        intro t ht
        show (if t ∈ Set.Icc (u k.castSucc) (u k.succ) then cp t else γ t) = γ t
        rw [if_neg ht]
      obtain ⟨H, hHcont, hHmem, hH0, hH1, hHends, hHout⟩ :=
        exists_path_homotopy_in_discRegion D₂ Φ hΦ huv
          (c := γ) (d := br) γ.cont hbrcont hD
          (fun t ht => D₂.interior_subset_carrier (hD₂ (hbr_mem t ht)))
          hbr_a.symm hbr_b.symm (fun t ht => (hbr_out t ht).symm)
      refine ⟨H, hHcont, fun s => hHends s, fun t ht => ⟨hH0 t, ?_, ?_⟩⟩
      · rw [hH1 t]
        show (if t ∈ Set.Icc (u k.castSucc) (u k.succ) then cp t else γ t) ∈ A
        rw [if_pos ht]
        exact (hjoin.somePath_mem _).1
      · intro s
        exact D₂.carrier_subset_surface (hHmem s t ht)
  -- ## Step 9: the glued family
  choose Q hQcont hQmatch hQrest using piece_data
  obtain ⟨G, hGcont, hGspec⟩ :=
    exists_glued_family u hu_strict γ γ.cont Q hQcont hQmatch
  have hG_carrier : ∀ s t : ℝ, t ∈ Set.Icc 0 (2 * Real.pi) → G s t ∈ P.carrier := by
    intro s t ht
    obtain ⟨k, hk⟩ := hpiece_cover t ht
    rw [hGspec k s t hk]
    exact (hQrest k t hk).2.2 s
  have hG_zero : ∀ s : ℝ, G s 0 = γ 0 := by
    intro s
    have hmem : (0 : ℝ) ∈ Set.Icc (u (⟨0, hMpos⟩ : Fin M).castSucc)
        (u (⟨0, hMpos⟩ : Fin M).succ) := by
      constructor
      · change u 0 ≤ 0
        rw [hu0]
      · rw [hu0.symm]
        exact hu_strict.monotone (by simp [Fin.le_def])
    rw [hGspec ⟨0, hMpos⟩ s 0 hmem]
    have h1 := (hQmatch ⟨0, hMpos⟩ s).1
    simpa [hu0] using h1
  have hklast : (⟨M - 1, by omega⟩ : Fin M).succ = Fin.last M :=
    Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
  have hG_twoPi : ∀ s : ℝ, G s (2 * Real.pi) = γ (2 * Real.pi) := by
    intro s
    have hmem : (2 * Real.pi) ∈ Set.Icc (u (⟨M - 1, by omega⟩ : Fin M).castSucc)
        (u (⟨M - 1, by omega⟩ : Fin M).succ) := by
      constructor
      · calc u (⟨M - 1, by omega⟩ : Fin M).castSucc
            ≤ u (⟨M - 1, by omega⟩ : Fin M).succ :=
              (hu_strict (Fin.castSucc_lt_succ : _ < _)).le
          _ = 2 * Real.pi := by rw [hklast, huM]
      · rw [hklast, huM]
    rw [hGspec ⟨M - 1, by omega⟩ s _ hmem]
    have h1 := (hQmatch ⟨M - 1, by omega⟩ s).2
    rw [hklast, huM] at h1
    exact h1
  have hG_per : ∀ s : ℝ, G s (2 * Real.pi) = G s 0 := by
    intro s
    have hp : γ (2 * Real.pi) = γ 0 := by
      simpa using (γ.periodic 0 : γ (0 + 2 * Real.pi) = γ 0)
    rw [hG_twoPi s, hG_zero s, hp]
  have hG_init : ∀ t : ℝ, t ∈ Set.Icc 0 (2 * Real.pi) → G 0 t = γ t := by
    intro t ht
    obtain ⟨k, hk⟩ := hpiece_cover t ht
    rw [hGspec k 0 t hk]
    exact (hQrest k t hk).1
  have hG_final : ∀ t : ℝ, t ∈ Set.Icc 0 (2 * Real.pi) → G 1 t ∈ A := by
    intro t ht
    obtain ⟨k, hk⟩ := hpiece_cover t ht
    rw [hGspec k 1 t hk]
    exact (hQrest k t hk).2.1
  obtain ⟨Gc, hGccont, hGcapply⟩ := Work.Smooth.Morse.Flow.exists_continuous_addCircle_lift G
    (hGcont.continuousOn.mono (Set.subset_univ _)) hG_per
  let ρ : ℝ → ℝ := fun t =>
    (AddCircle.equivIco (2 * Real.pi) (0 : ℝ) (t : AddCircle (2 * Real.pi)) : ℝ)
  have hρ_mem : ∀ t : ℝ, ρ t ∈ Set.Icc 0 (2 * Real.pi) := by
    intro t
    show (AddCircle.equivIco (2 * Real.pi) (0 : ℝ)
      (t : AddCircle (2 * Real.pi)) : ℝ) ∈ Set.Icc 0 (2 * Real.pi)
    have h := (AddCircle.equivIco (2 * Real.pi) (0 : ℝ) (t : AddCircle (2 * Real.pi))).2
    exact ⟨h.1, le_of_lt (by simpa only [zero_add] using h.2)⟩
  have hρ_coe : ∀ t : ℝ, ((ρ t : ℝ) : AddCircle (2 * Real.pi)) =
      (t : AddCircle (2 * Real.pi)) := fun t =>
    AddCircle.coe_equivIco (p := 2 * Real.pi) (a := (0 : ℝ))
      (y := (t : AddCircle (2 * Real.pi)))
  let H : ℝ → ℝ → R3 := fun s t => Gc (s, (t : AddCircle (2 * Real.pi)))
  have hHapply : ∀ s t : ℝ, H s t = G s (ρ t) := by
    intro s t
    show Gc (s, (t : AddCircle (2 * Real.pi))) = G s (ρ t)
    rw [← hρ_coe t, hGcapply s (ρ t) (hρ_mem t)]
  have hHcont : Continuous (Function.uncurry H) := by
    have hcoe : Continuous fun t : ℝ => (t : AddCircle (2 * Real.pi)) := continuous_quotient_mk'
    have hc : Continuous (fun p : ℝ × ℝ => Gc (p.1, (p.2 : AddCircle (2 * Real.pi)))) :=
      hGccont.comp (continuous_fst.prodMk (hcoe.comp continuous_snd))
    exact hc
  have hHper : ∀ s t : ℝ, H s (t + 2 * Real.pi) = H s t := by
    intro s t
    show Gc (s, ((t + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi))) =
      Gc (s, (t : AddCircle (2 * Real.pi)))
    rw [AddCircle.coe_add_period]
  have hHmem : ∀ s t : ℝ, H s t ∈ P.carrier := by
    intro s t
    rw [hHapply s t]
    exact hG_carrier s (ρ t) (hρ_mem t)
  have hH0 : ∀ t : ℝ, H 0 t = γ t := by
    intro t
    rw [hHapply 0 t, hG_init (ρ t) (hρ_mem t)]
    have hper : Function.Periodic γ.γ (2 * Real.pi) := γ.periodic
    rw [← hper.lift_coe (ρ t), ← hper.lift_coe t, hρ_coe t]
  have hH1 : ∀ t : ℝ, H 1 t ∈ A := by
    intro t
    rw [hHapply 1 t]
    exact hG_final (ρ t) (hρ_mem t)
  refine ⟨⟨fun t => H 1 t, ?_, ?_, ?_⟩, fun t => hH1 t, ?_⟩
  · exact hHcont.comp (continuous_const.prodMk continuous_id)
  · intro t; exact hHper 1 t
  · intro t; exact hHmem 1 t
  · exact ⟨H, hHcont, hHmem, hH0, fun t => rfl, hHper⟩


/-! ## The target -/

theorem discAttach_clusters {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hB : B ⊆ D.carrier)
    (hBopen : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hcl : ∀ x : LeanEval.KnotTheory.PardonDistortion.R3, x ∈ P.carrier →
      x ∈ closure B → x ∉ B → x ∈ A)
    (hconn : ∀ p : LeanEval.KnotTheory.PardonDistortion.R3, p ∈ closure B → p ∉ B →
      ∀ q : LeanEval.KnotTheory.PardonDistortion.R3, q ∈ closure B → q ∉ B →
      JoinedIn (A ∩ D.carrier) p q) :
    ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A ∪ B) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ A) ∧
        Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ := by
  intro γ hγAB
  classical
  have hSopen : IsOpen (γ ⁻¹' B) := by
    have hcont : Continuous fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier) :=
      γ.cont.subtype_mk γ.mem
    exact hBopen.preimage hcont
  by_cases hfr : (frontier (γ ⁻¹' B)).Nonempty
  · -- ## the main case: a frontier point exists, shift the parametrisation to it
    obtain ⟨θ, hθ⟩ := hfr
    have hθmem : γ θ ∈ closure B ∧ γ θ ∉ B := frontier_preimage_mem hSopen hθ
    set γθ : Work.CoreTopology.ClosedCurve P :=
      { γ := fun t : ℝ => γ (t + θ)
        cont := γ.cont.comp (continuous_id.add continuous_const)
        periodic := by
          intro t
          rw [show t + 2 * Real.pi + θ = (t + θ) + 2 * Real.pi from by ring]
          exact γ.periodic (t + θ)
        mem := fun t => γ.mem (t + θ) } with hγθdef
    have hγθAB : ∀ t : ℝ, γθ t ∈ A ∪ B := fun t => hγAB (t + θ)
    have hγθ0 : γθ 0 ∈ closure B ∧ γθ 0 ∉ B := by
      have h : γθ 0 = γ θ := by
        show γ (0 + θ) = γ θ
        rw [zero_add]
      rw [h]; exact hθmem
    obtain ⟨γ', hγ'A, hhom⟩ :=
      exists_curve_homotopic_into_A hB hBopen hcl hconn γθ hγθAB hγθ0
    refine ⟨γ', hγ'A, ?_⟩
    have hshift : Work.CoreTopology.Homotopic P γ γθ :=
      ⟨fun s t => γ (t + s * θ), by
          exact γ.cont.comp (continuous_snd.add (continuous_fst.mul continuous_const)),
        fun s t => γ.mem (t + s * θ),
        fun t => by
          show γ (t + 0 * θ) = γ t
          rw [zero_mul, add_zero],
        fun t => by
          show γ (t + 1 * θ) = γθ t
          rw [one_mul],
        fun s t => by
          show γ ((t + 2 * Real.pi) + s * θ) = γ (t + s * θ)
          rw [show (t + 2 * Real.pi) + s * θ = (t + s * θ) + 2 * Real.pi from by ring]
          exact γ.periodic (t + s * θ)⟩
    rw [← Work.SurgeryInvariance.WindingOf.homotopic_eq hhom,
      Work.SurgeryInvariance.WindingOf.homotopic_eq hshift]
  · -- ## degenerate case: the frontier is empty, so `γ ⁻¹' B` is all or nothing
    have hempty : frontier (γ ⁻¹' B) = ∅ := Set.not_nonempty_iff_eq_empty.mp hfr
    rcases (frontier_eq_empty_iff.mp hempty) with hS | hS
    · -- `γ` already lies in `A`
      refine ⟨γ, fun t => ?_, rfl⟩
      rcases hγAB t with h | h
      · exact h
      · exfalso
        have : t ∈ γ ⁻¹' B := h
        rw [hS] at this
        exact this
    · -- `γ` lies in `B`, hence in the disc `D`: it is null-homotopic, and any constant
      -- curve of `A` has the same (zero) winding vector
      have hSB : ∀ t : ℝ, γ t ∈ B := by
        intro t
        have : t ∈ γ ⁻¹' B := by rw [hS]; exact Set.mem_univ t
        exact this
      have hex : ∃ x : R3, x ∈ closure B ∧ x ∉ B := by
        by_contra hcon
        push_neg at hcon
        have hcl_eq : closure B = B := Set.Subset.antisymm hcon subset_closure
        have hclosed : IsClosed (Subtype.val ⁻¹' B : Set P.carrier) := by
          have h1 : (Subtype.val ⁻¹' B : Set P.carrier) = Subtype.val ⁻¹' closure B := by
            ext y
            constructor
            · intro hy; exact subset_closure hy
            · intro hy
              rw [hcl_eq] at hy
              exact hy
          rw [h1]
          exact isClosed_closure.preimage continuous_subtype_val
        haveI : PreconnectedSpace P.carrier :=
          isPreconnected_iff_preconnectedSpace.mp (isPreconnected_range P.cont)
        have hclop : IsClopen (Subtype.val ⁻¹' B : Set P.carrier) := ⟨hclosed, hBopen⟩
        rcases isClopen_iff.mp hclop with h | h
        · have h2 : (⟨γ 0, γ.mem 0⟩ : P.carrier) ∈
              (Subtype.val ⁻¹' B : Set P.carrier) := hSB 0
          rw [h] at h2
          exact h2
        · refine not_carrier_subset_discRegion D (fun x hx => ?_)
          have h2 : (⟨x, hx⟩ : P.carrier) ∈ (Subtype.val ⁻¹' B : Set P.carrier) := by
            rw [h]; exact Set.mem_univ _
          exact hB h2
      obtain ⟨x, hxcl, hxB⟩ := hex
      have hxcar : x ∈ P.carrier := closure_subset_surface D hB hxcl
      have hxA : x ∈ A := hcl x hxcar hxcl hxB
      refine ⟨Work.InnermostDisk.constCurve P x hxcar, fun t => hxA, ?_⟩
      rw [windingOf_constCurve x hxcar]
      obtain ⟨y, hy, hhy⟩ := homotopic_const_of_subset_discRegion D (fun t => hB (hSB t))
      rw [Work.SurgeryInvariance.WindingOf.homotopic_eq hhy, windingOf_constCurve y hy]


end

end Work.Drive.EpsForm
