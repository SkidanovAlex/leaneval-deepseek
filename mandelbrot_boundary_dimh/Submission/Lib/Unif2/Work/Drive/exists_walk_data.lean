import Mathlib
import Submission.Lib.Unif2.Work.Drive.cBallDefs
import Submission.Lib.Unif2.Work.Drive.exists_locallyFinite_openCoordinateBall_cover
import Submission.Lib.Unif2.Work.Drive.exists_nerve_escaping_walk
import Submission.Lib.Unif2.Work.Drive.exists_phase_plan

open Set Metric Filter
open Classical
open scoped Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.Drive

section Machinery


variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## FineChain helpers -/

theorem fineChain_cons_cons {c : OpenPartialHomeomorph X ℂ} {x u w : X} {r : ℝ} {rest : List X} :
    FineChain c x r (u :: w :: rest) ↔
      (dist (c w) (c u) < (r - dist (c u) (c x)) / 8 ∧ FineChain c x r (w :: rest)) :=
  Iff.rfl

theorem fineChain_singleton {c : OpenPartialHomeomorph X ℂ} {x u : X} {r : ℝ} :
    FineChain c x r [u] := trivial

theorem fineChain_nil {c : OpenPartialHomeomorph X ℂ} {x : X} {r : ℝ} :
    FineChain c x r [] := trivial

/-! ## The machine -/

/-- State of the walk machine. -/
structure WalkState (X : Type*) where
  pt : X
  rem : List X
  j : ℕ
  forb : Set X

/-- The conclusion of `exists_phase_plan`, packaged (with a *set* of forbidden points). -/
def IsPhasePlan (U : ℕ → Set X) (c₀ : ℕ → X) (r₀ : ℕ → ℝ) (v : ℕ → ℕ) (j : ℕ) (p : X)
    (F : Set X) (z : X × List X) : Prop :=
  z.1 ∈ U (v j) ∩ U (v (j + 1)) ∧ z.1 ∉ F ∧ z.1 ≠ p ∧
  z.2.head? = some p ∧ z.2.getLast? = some z.1 ∧ z.2.Nodup ∧
  (∀ y ∈ z.2, y ∈ U (v j) ∧ y ∉ F) ∧
  FineChain (chartAt ℂ (c₀ (v j))) (c₀ (v j)) (r₀ (v j)) z.2

/-- One transition of the walk machine. -/
def walkStep (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (s : WalkState X) : WalkState X :=
  match s.rem with
  | [] =>
      match plan s.pt s.j s.forb with
      | (_, _ :: x₂ :: rest) =>
          match rest with
          | [] => ⟨x₂, [], s.j + 1, insert s.pt s.forb⟩
          | _ :: _ => ⟨x₂, rest, s.j, insert s.pt s.forb⟩
      | _ => s
  | y :: t =>
      match t with
      | [] => ⟨y, [], s.j + 1, insert s.pt s.forb⟩
      | _ :: _ => ⟨y, t, s.j, insert s.pt s.forb⟩

/-- The invariant kept by the machine. -/
structure WalkInv (U : ℕ → Set X) (c₀ : ℕ → X) (r₀ : ℕ → ℝ) (v : ℕ → ℕ)
    (s : WalkState X) : Prop where
  pt_mem : s.pt ∈ U (v s.j)
  rem_mem : ∀ y ∈ s.rem, y ∈ U (v s.j)
  pt_forb : s.pt ∉ s.forb
  rem_forb : ∀ y ∈ s.rem, y ∉ s.forb
  forb_fin : s.forb.Finite
  fine : FineChain (chartAt ℂ (c₀ (v s.j))) (c₀ (v s.j)) (r₀ (v s.j)) (s.pt :: s.rem)
  last_mem : ∀ y, s.rem.getLast? = some y → y ∈ U (v (s.j + 1))
  nodup : (s.pt :: s.rem).Nodup

/-- The run of the machine. -/
def walkRun (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (init : WalkState X) (n : ℕ) : WalkState X :=
  Nat.rec init (fun _ s => walkStep U v plan s) n

/-! ## Computation lemmas for `walkStep` -/

theorem walkStep_cons_single (U : ℕ → Set X) (v : ℕ → ℕ)
    (plan : X → ℕ → Set X → X × List X) (s : WalkState X) {y : X} (h : s.rem = [y]) :
    walkStep U v plan s = ⟨y, [], s.j + 1, insert s.pt s.forb⟩ := by
  rcases s with ⟨pt, rem, j, forb⟩
  have h' : rem = [y] := h
  simp only [walkStep]
  rw [h']

theorem walkStep_cons_cons (U : ℕ → Set X) (v : ℕ → ℕ)
    (plan : X → ℕ → Set X → X × List X) (s : WalkState X) {y u : X} {t : List X}
    (h : s.rem = y :: u :: t) :
    walkStep U v plan s = ⟨y, u :: t, s.j, insert s.pt s.forb⟩ := by
  rcases s with ⟨pt, rem, j, forb⟩
  have h' : rem = y :: u :: t := h
  simp only [walkStep]
  rw [h']

theorem walkStep_nil_nil (U : ℕ → Set X) (v : ℕ → ℕ)
    (plan : X → ℕ → Set X → X × List X) (s : WalkState X) (h : s.rem = [])
    (hp : (plan s.pt s.j s.forb).2 = []) : walkStep U v plan s = s := by
  rcases s with ⟨pt, rem, j, forb⟩
  have h' : rem = [] := h
  have hp' : (plan pt j forb).2 = [] := hp
  simp only [walkStep]
  rw [h']
  rcases hz : plan pt j forb with ⟨q, l⟩
  rw [hz] at hp'
  have hpl : l = [] := by simpa using hp'
  rw [hpl]

theorem walkStep_nil_two (U : ℕ → Set X) (v : ℕ → ℕ)
    (plan : X → ℕ → Set X → X × List X) (s : WalkState X) (h : s.rem = []) {y x : X}
    (hp : (plan s.pt s.j s.forb).2 = y :: x :: []) :
    walkStep U v plan s = ⟨x, [], s.j + 1, insert s.pt s.forb⟩ := by
  rcases s with ⟨pt, rem, j, forb⟩
  have h' : rem = [] := h
  have hp' : (plan pt j forb).2 = y :: x :: [] := hp
  simp only [walkStep]
  rw [h']
  rcases hz : plan pt j forb with ⟨q, l⟩
  rw [hz] at hp'
  have hpl : l = y :: x :: [] := by simpa using hp'
  rw [hpl]

theorem walkStep_nil_three (U : ℕ → Set X) (v : ℕ → ℕ)
    (plan : X → ℕ → Set X → X × List X) (s : WalkState X) (h : s.rem = []) {y x u : X}
    {rest : List X} (hp : (plan s.pt s.j s.forb).2 = y :: x :: u :: rest) :
    walkStep U v plan s = ⟨x, u :: rest, s.j, insert s.pt s.forb⟩ := by
  rcases s with ⟨pt, rem, j, forb⟩
  have h' : rem = [] := h
  have hp' : (plan pt j forb).2 = y :: x :: u :: rest := hp
  simp only [walkStep]
  rw [h']
  rcases hz : plan pt j forb with ⟨q, l⟩
  rw [hz] at hp'
  have hpl : l = y :: x :: u :: rest := by simpa using hp'
  rw [hpl]

/-! ## The planning function -/

/-- A planning function is good if it realises `exists_phase_plan` wherever it is applicable. -/
def IsGoodPlan (U : ℕ → Set X) (c₀ : ℕ → X) (r₀ : ℕ → ℝ) (v : ℕ → ℕ)
    (plan : X → ℕ → Set X → X × List X) : Prop :=
  ∀ (pt : X) (j : ℕ) (F : Set X), F.Finite → pt ∈ U (v j) → pt ∉ F →
    IsPhasePlan U c₀ r₀ v j pt F (plan pt j F)

theorem exists_phase_plan_set {U : ℕ → Set X} (hUo : ∀ n, IsOpen (U n)) {c₀ : ℕ → X} {r₀ : ℕ → ℝ}
    (hU : ∀ n, U n = (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n))
    (hroom : ∀ n, Metric.closedBall ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) ⊆ (chartAt ℂ (c₀ n)).target)
    {v : ℕ → ℕ} {j : ℕ} {p : X} {F : Set X} (hF : F.Finite)
    (hp : p ∈ U (v j)) (hpF : p ∉ F) (hadj : (U (v j) ∩ U (v (j + 1))).Nonempty) :
    ∃ z : X × List X, IsPhasePlan U c₀ r₀ v j p F z := by
  obtain ⟨z, hz⟩ :=
    exists_phase_plan (F := hF.toFinset) U hUo c₀ r₀ hU hroom hp
      (by rw [hF.coe_toFinset]; exact hpF) hadj
  exact ⟨z, by simpa [IsPhasePlan, hF.coe_toFinset] using hz⟩

noncomputable def mkPlan (U : ℕ → Set X) (c₀ : ℕ → X) (r₀ : ℕ → ℝ) (v : ℕ → ℕ)
    (hUo : ∀ n, IsOpen (U n))
    (hU : ∀ n, U n = (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n))
    (hroom : ∀ n, Metric.closedBall ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) ⊆ (chartAt ℂ (c₀ n)).target)
    (hadj : ∀ j, (U (v j) ∩ U (v (j + 1))).Nonempty) :
    X → ℕ → Set X → X × List X :=
  fun pt j F => if h : F.Finite ∧ pt ∈ U (v j) ∧ pt ∉ F then
      Classical.choose (exists_phase_plan_set hUo hU hroom h.1 h.2.1 h.2.2 (hadj j))
    else (pt, [pt])

theorem mkPlan_spec (U : ℕ → Set X) (c₀ : ℕ → X) (r₀ : ℕ → ℝ) (v : ℕ → ℕ)
    (hUo : ∀ n, IsOpen (U n))
    (hU : ∀ n, U n = (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n))
    (hroom : ∀ n, Metric.closedBall ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) ⊆ (chartAt ℂ (c₀ n)).target)
    (hadj : ∀ j, (U (v j) ∩ U (v (j + 1))).Nonempty) :
    IsGoodPlan U c₀ r₀ v (mkPlan U c₀ r₀ v hUo hU hroom hadj) := by
  intro pt j F hF hp hpF
  unfold mkPlan
  rw [dif_pos ⟨hF, hp, hpF⟩]
  exact Classical.choose_spec (exists_phase_plan_set hUo hU hroom hF hp hpF (hadj j))

/-! ## Initial invariant -/

theorem walkInv_init {U : ℕ → Set X} {c₀ : ℕ → X} {r₀ : ℕ → ℝ} {v : ℕ → ℕ} {z₀ : X}
    {n₀ : ℕ} (hv0 : v 0 = n₀) (hz₀ : z₀ ∈ U n₀) :
    WalkInv U c₀ r₀ v ⟨z₀, [], 0, (∅ : Set X)⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show z₀ ∈ U (v 0); rw [hv0]; exact hz₀
  · intro y hy; simp at hy
  · show z₀ ∉ (∅ : Set X); simp
  · intro y hy; simp at hy
  · exact Set.finite_empty
  · exact fineChain_singleton
  · intro y hy; simp at hy
  · simp

theorem walkStep_master {U : ℕ → Set X} {c₀ : ℕ → X} {r₀ : ℕ → ℝ} {v : ℕ → ℕ}
    {plan : X → ℕ → Set X → X × List X} (hplan : IsGoodPlan U c₀ r₀ v plan)
    (s : WalkState X) (hs : WalkInv U c₀ r₀ v s) :
    ∃ (pt' : X) (rem' : List X) (j' : ℕ),
      walkStep U v plan s = ⟨pt', rem', j', insert s.pt s.forb⟩ ∧
      WalkInv U c₀ r₀ v ⟨pt', rem', j', insert s.pt s.forb⟩ ∧
      pt' ∈ U (v s.j) ∧ pt' ∉ s.forb ∧ pt' ≠ s.pt ∧
      dist ((chartAt ℂ (c₀ (v s.j))) pt') ((chartAt ℂ (c₀ (v s.j))) s.pt) <
        (r₀ (v s.j) - dist ((chartAt ℂ (c₀ (v s.j))) s.pt)
          ((chartAt ℂ (c₀ (v s.j))) (c₀ (v s.j)))) / 8 := by
  rcases s with ⟨pt, rem, j, forb⟩
  cases rem with
  | nil =>
    have hspec := hplan pt j forb hs.forb_fin hs.pt_mem hs.pt_forb
    rcases hz : plan pt j forb with ⟨q, l⟩
    rw [hz] at hspec
    simp only [IsPhasePlan] at hspec
    obtain ⟨hq_mem, hq_forb, hq_ne, hhead, hlast, hnodup, hmem, hfine⟩ := hspec
    cases l with
    | nil => exact absurd hhead (by simp)
    | cons x₁ l' =>
      have hx₁ : x₁ = pt := by simpa using hhead
      cases l' with
      | nil =>
        have hqpt : q = pt := by
          have h : x₁ = q := by simpa using hlast
          rw [hx₁] at h
          exact h.symm
        exact absurd hqpt hq_ne
      | cons x₂ rest =>
        have hx₂_ne : x₂ ≠ pt := by
          intro h
          have h' : x₁ = x₂ := by rw [hx₁, h]
          have hmem' : x₁ ∈ x₂ :: rest := by rw [h']; exact List.mem_cons_self
          exact (List.nodup_cons.mp hnodup).1 hmem'
        have hx₂_mem : x₂ ∈ U (v j) := (hmem x₂ (by simp)).1
        have hx₂_forb : x₂ ∉ forb := (hmem x₂ (by simp)).2
        have hx₂_fine : FineChain (chartAt ℂ (c₀ (v j))) (c₀ (v j)) (r₀ (v j)) (x₂ :: rest) :=
          (fineChain_cons_cons.mp hfine).2
        have hx₂_bound : dist ((chartAt ℂ (c₀ (v j))) x₂) ((chartAt ℂ (c₀ (v j))) pt) <
            (r₀ (v j) - dist ((chartAt ℂ (c₀ (v j))) pt)
              ((chartAt ℂ (c₀ (v j))) (c₀ (v j)))) / 8 := by
          have h := (fineChain_cons_cons.mp hfine).1
          rwa [hx₁] at h
        cases rest with
        | nil =>
          have hx₂q : x₂ = q := by simpa using hlast
          refine ⟨x₂, [], j + 1, ?_, ?_, hx₂_mem, hx₂_forb, hx₂_ne, hx₂_bound⟩
          · exact walkStep_nil_two U v plan ⟨pt, [], j, forb⟩ rfl (by rw [hz])
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · show x₂ ∈ U (v (j + 1)); rw [hx₂q]; exact hq_mem.2
            · intro z hz'; simp at hz'
            · show x₂ ∉ insert pt forb
              rw [Set.mem_insert_iff]
              rintro (h | h)
              · exact hx₂_ne h
              · exact hx₂_forb h
            · intro z hz'; simp at hz'
            · exact hs.forb_fin.insert pt
            · exact fineChain_singleton
            · intro z hz'; exact absurd hz' (by simp)
            · simp
        | cons u rest' =>
          refine ⟨x₂, u :: rest', j, ?_, ?_, hx₂_mem, hx₂_forb, hx₂_ne, hx₂_bound⟩
          · exact walkStep_nil_three U v plan ⟨pt, [], j, forb⟩ rfl (by rw [hz])
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact hx₂_mem
            · intro z hz'
              exact (hmem z (List.mem_cons_of_mem x₁ (List.mem_cons_of_mem x₂ hz'))).1
            · show x₂ ∉ insert pt forb
              rw [Set.mem_insert_iff]
              rintro (h | h)
              · exact hx₂_ne h
              · exact hx₂_forb h
            · intro z hz'
              have hzp : z ≠ pt := by
                intro h
                have hmem' : x₁ ∈ x₂ :: u :: rest' := by
                  rw [hx₁, ← h]
                  exact List.mem_cons_of_mem x₂ hz'
                exact (List.nodup_cons.mp hnodup).1 hmem'
              show z ∉ insert pt forb
              rw [Set.mem_insert_iff]
              rintro (h | h)
              · exact hzp h
              · exact (hmem z (List.mem_cons_of_mem x₁ (List.mem_cons_of_mem x₂ hz'))).2 h
            · exact hs.forb_fin.insert pt
            · exact hx₂_fine
            · intro z hz'
              have h1 : (x₁ :: x₂ :: u :: rest').getLast? = some z := by simpa using hz'
              rw [hlast] at h1
              have hzq : z = q := by simpa using h1.symm
              rw [hzq]; exact hq_mem.2
            · exact (List.nodup_cons.mp hnodup).2
  | cons y t =>
    cases t with
    | nil =>
      have hy_last : y ∈ U (v (j + 1)) := hs.last_mem y (by simp)
      have hy_mem : y ∈ U (v j) := hs.rem_mem y (by simp)
      have hy_forb : y ∉ forb := hs.rem_forb y (by simp)
      have hy_ne : y ≠ pt := by
        intro h
        have h' : pt ∈ y :: ([] : List X) := by rw [← h]; exact List.mem_cons_self
        exact (List.nodup_cons.mp hs.nodup).1 h'
      have hbound : dist ((chartAt ℂ (c₀ (v j))) y) ((chartAt ℂ (c₀ (v j))) pt) <
          (r₀ (v j) - dist ((chartAt ℂ (c₀ (v j))) pt)
            ((chartAt ℂ (c₀ (v j))) (c₀ (v j)))) / 8 :=
        (fineChain_cons_cons.mp hs.fine).1
      refine ⟨y, [], j + 1, ?_, ?_, hy_mem, hy_forb, hy_ne, hbound⟩
      · exact walkStep_cons_single U v plan ⟨pt, [y], j, forb⟩ rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hy_last
        · intro z hz'; simp at hz'
        · show y ∉ insert pt forb
          rw [Set.mem_insert_iff]
          rintro (h | h)
          · exact hy_ne h
          · exact hy_forb h
        · intro z hz'; simp at hz'
        · exact hs.forb_fin.insert pt
        · exact fineChain_singleton
        · intro z hz'; exact absurd hz' (by simp)
        · simp
    | cons u t' =>
      have hy_mem : y ∈ U (v j) := hs.rem_mem y (by simp)
      have hy_forb : y ∉ forb := hs.rem_forb y (by simp)
      have hy_ne : y ≠ pt := by
        intro h
        have h' : pt ∈ y :: u :: t' := by rw [← h]; exact List.mem_cons_self
        exact (List.nodup_cons.mp hs.nodup).1 h'
      have hbound : dist ((chartAt ℂ (c₀ (v j))) y) ((chartAt ℂ (c₀ (v j))) pt) <
          (r₀ (v j) - dist ((chartAt ℂ (c₀ (v j))) pt)
            ((chartAt ℂ (c₀ (v j))) (c₀ (v j)))) / 8 :=
        (fineChain_cons_cons.mp hs.fine).1
      refine ⟨y, u :: t', j, ?_, ?_, hy_mem, hy_forb, hy_ne, hbound⟩
      · exact walkStep_cons_cons U v plan ⟨pt, y :: u :: t', j, forb⟩ rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hy_mem
        · intro z hz'; exact hs.rem_mem z (List.mem_cons_of_mem y hz')
        · show y ∉ insert pt forb
          rw [Set.mem_insert_iff]
          rintro (h | h)
          · exact hy_ne h
          · exact hy_forb h
        · intro z hz'
          have hzp : z ≠ pt := by
            intro h
            have hmem' : pt ∈ y :: u :: t' := by
              rw [← h]
              exact List.mem_cons_of_mem y hz'
            exact (List.nodup_cons.mp hs.nodup).1 hmem'
          show z ∉ insert pt forb
          rw [Set.mem_insert_iff]
          rintro (h | h)
          · exact hzp h
          · exact (hs.rem_forb z (List.mem_cons_of_mem y hz')) h
        · exact hs.forb_fin.insert pt
        · exact (fineChain_cons_cons.mp hs.fine).2
        · intro z hz'
          have h1 : (y :: u :: t').getLast? = some z := by simpa using hz'
          exact hs.last_mem z h1
        · exact (List.nodup_cons.mp hs.nodup).2

/-! ## Consequences of the master lemma -/

theorem walkInv_step {U : ℕ → Set X} {c₀ : ℕ → X} {r₀ : ℕ → ℝ} {v : ℕ → ℕ}
    {plan : X → ℕ → Set X → X × List X} (hplan : IsGoodPlan U c₀ r₀ v plan) (s : WalkState X)
    (hs : WalkInv U c₀ r₀ v s) : WalkInv U c₀ r₀ v (walkStep U v plan s) := by
  obtain ⟨pt', rem', j', heq, hinv', -⟩ := walkStep_master hplan s hs
  rw [heq]; exact hinv'

theorem walkStep_forb {U : ℕ → Set X} {c₀ : ℕ → X} {r₀ : ℕ → ℝ} {v : ℕ → ℕ}
    {plan : X → ℕ → Set X → X × List X} (hplan : IsGoodPlan U c₀ r₀ v plan) (s : WalkState X)
    (hs : WalkInv U c₀ r₀ v s) :
    (walkStep U v plan s).forb = insert s.pt s.forb := by
  obtain ⟨pt', rem', j', heq, -⟩ := walkStep_master hplan s hs
  rw [heq]

theorem walkStep_step_facts {U : ℕ → Set X} {c₀ : ℕ → X} {r₀ : ℕ → ℝ} {v : ℕ → ℕ}
    {plan : X → ℕ → Set X → X × List X} (hplan : IsGoodPlan U c₀ r₀ v plan) (s : WalkState X)
    (hs : WalkInv U c₀ r₀ v s) :
    (walkStep U v plan s).pt ∈ U (v s.j) ∧
    (walkStep U v plan s).pt ∉ s.forb ∧
    (walkStep U v plan s).pt ≠ s.pt ∧
    dist ((chartAt ℂ (c₀ (v s.j))) (walkStep U v plan s).pt) ((chartAt ℂ (c₀ (v s.j))) s.pt) <
      (r₀ (v s.j) - dist ((chartAt ℂ (c₀ (v s.j))) s.pt)
        ((chartAt ℂ (c₀ (v s.j))) (c₀ (v s.j)))) / 8 := by
  obtain ⟨pt', rem', j', heq, -, hmem, hforb, hne, hbound⟩ := walkStep_master hplan s hs
  rw [heq]
  exact ⟨hmem, hforb, hne, hbound⟩

/-! ## The machine makes progress -/

theorem walkStep_nil_one (U : ℕ → Set X) (v : ℕ → ℕ)
    (plan : X → ℕ → Set X → X × List X) (s : WalkState X) (h : s.rem = []) {x : X}
    (hp : (plan s.pt s.j s.forb).2 = [x]) :
    walkStep U v plan s = s := by
  rcases s with ⟨pt, rem, j, forb⟩
  have h' : rem = [] := h
  have hp' : (plan pt j forb).2 = [x] := hp
  simp only [walkStep]
  rw [h']
  rcases hz : plan pt j forb with ⟨q, l⟩
  rw [hz] at hp'
  have hpl : l = [x] := by simpa using hp'
  rw [hpl]

theorem walkStep_j_le (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (s : WalkState X) : s.j ≤ (walkStep U v plan s).j := by
  rcases s with ⟨pt, rem, j, forb⟩
  cases rem with
  | cons y t =>
    cases t with
    | nil =>
      rw [walkStep_cons_single U v plan ⟨pt, [y], j, forb⟩ rfl]
      exact Nat.le_succ j
    | cons u t' =>
      rw [walkStep_cons_cons U v plan ⟨pt, y :: u :: t', j, forb⟩ rfl]
  | nil =>
    rcases hz : plan pt j forb with ⟨q, l⟩
    cases l with
    | nil =>
      rw [walkStep_nil_nil U v plan ⟨pt, [], j, forb⟩ rfl (by rw [hz])]
    | cons x₁ l' =>
      cases l' with
      | nil =>
        rw [walkStep_nil_one U v plan ⟨pt, [], j, forb⟩ rfl (by rw [hz])]
      | cons x₂ rest =>
        cases rest with
        | nil =>
          rw [walkStep_nil_two U v plan ⟨pt, [], j, forb⟩ rfl (by rw [hz])]
          exact Nat.le_succ j
        | cons u rest' =>
          rw [walkStep_nil_three U v plan ⟨pt, [], j, forb⟩ rfl (by rw [hz])]

theorem walkStep_rem_cons (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (s : WalkState X) {y : X} {t : List X} (h : s.rem = y :: t) :
    (walkStep U v plan s).rem = t := by
  rcases s with ⟨pt, rem, j, forb⟩
  have h' : rem = y :: t := h
  subst h'
  cases t with
  | nil => rw [walkStep_cons_single U v plan ⟨pt, [y], j, forb⟩ rfl]
  | cons u t' => rw [walkStep_cons_cons U v plan ⟨pt, y :: u :: t', j, forb⟩ rfl]

theorem walkStep_j_cons_cons (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (s : WalkState X) {y u : X} {t : List X} (h : s.rem = y :: u :: t) :
    (walkStep U v plan s).j = s.j := by
  rw [walkStep_cons_cons U v plan s h]

theorem walkStep_j_cons_single (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (s : WalkState X) {y : X} (h : s.rem = [y]) :
    (walkStep U v plan s).j = s.j + 1 := by
  rw [walkStep_cons_single U v plan s h]

theorem advance_of_rem (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X) :
    ∀ (l : List X) (s : WalkState X), s.rem = l → l ≠ [] →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ l.length ∧ ((walkStep U v plan)^[k] s).rem = [] ∧
        s.j + 1 ≤ ((walkStep U v plan)^[k] s).j := by
  intro l
  induction l with
  | nil => intro s h hne; exact absurd rfl hne
  | cons y l' ih =>
    intro s h _
    cases l' with
    | nil =>
      refine ⟨1, le_refl 1, by simp, ?_, ?_⟩
      · rw [Function.iterate_one, walkStep_rem_cons U v plan s h]
      · rw [Function.iterate_one, walkStep_j_cons_single U v plan s h]
    | cons u t =>
      have h1 : ((walkStep U v plan)^[1] s).rem = u :: t := by
        rw [Function.iterate_one]; exact walkStep_rem_cons U v plan s h
      have h2 : (walkStep U v plan s).j = s.j := walkStep_j_cons_cons U v plan s h
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (walkStep U v plan s) h1 (by simp)
      refine ⟨k + 1, ?_, ?_, ?_, ?_⟩
      · omega
      · simp only [List.length_cons] at hk2 ⊢; omega
      · rw [Function.iterate_succ_apply]; exact hk3
      · rw [Function.iterate_succ_apply, ← h2]; exact hk4

theorem j_advance_eventually {U : ℕ → Set X} {c₀ : ℕ → X} {r₀ : ℕ → ℝ} {v : ℕ → ℕ}
    {plan : X → ℕ → Set X → X × List X} (hplan : IsGoodPlan U c₀ r₀ v plan) (s : WalkState X)
    (hs : WalkInv U c₀ r₀ v s) :
    ∃ N : ℕ, 1 ≤ N ∧ s.j + 1 ≤ ((walkStep U v plan)^[N] s).j := by
  cases hrem : s.rem with
  | cons y t =>
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := advance_of_rem U v plan (y :: t) s hrem (by simp)
    exact ⟨k, hk1, hk4⟩
  | nil =>
    have hspec := hplan s.pt s.j s.forb hs.forb_fin hs.pt_mem hs.pt_forb
    rcases hz : plan s.pt s.j s.forb with ⟨q, l⟩
    rw [hz] at hspec
    simp only [IsPhasePlan] at hspec
    obtain ⟨hq_mem, hq_forb, hq_ne, hhead, hlast, hnodup, hmem, hfine⟩ := hspec
    cases l with
    | nil => exact absurd hhead (by simp)
    | cons x₁ l' =>
      cases l' with
      | nil =>
        have hx₁q : x₁ = q := by simpa using hlast
        have hx₁p : x₁ = s.pt := by simpa using hhead
        exact absurd (hx₁q.symm.trans hx₁p) hq_ne
      | cons x₂ rest =>
        cases rest with
        | nil =>
          refine ⟨1, le_refl 1, ?_⟩
          rw [Function.iterate_one, walkStep_nil_two U v plan s hrem (by rw [hz])]
        | cons u t =>
          have hst : walkStep U v plan s = ⟨x₂, u :: t, s.j, insert s.pt s.forb⟩ :=
            walkStep_nil_three U v plan s hrem (by rw [hz])
          have hrem' : (walkStep U v plan s).rem = u :: t := by rw [hst]
          obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
            advance_of_rem U v plan (u :: t) (walkStep U v plan s) hrem' (by simp)
          have hj : (walkStep U v plan s).j = s.j := by rw [hst]
          refine ⟨k + 1, ?_, ?_⟩
          · omega
          · rw [Function.iterate_succ_apply, ← hj]
            exact hk4

theorem walkRun_add (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (init : WalkState X) (n k : ℕ) :
    walkRun U v plan init (n + k) = ((walkStep U v plan)^[k]) (walkRun U v plan init n) := by
  induction k with
  | zero => simp [walkRun]
  | succ k ih =>
    rw [Nat.add_succ, Function.iterate_succ_apply']
    show walkStep U v plan (walkRun U v plan init (n + k))
      = walkStep U v plan ((walkStep U v plan)^[k] (walkRun U v plan init n))
    rw [ih]

theorem walkRun_j_mono (U : ℕ → Set X) (v : ℕ → ℕ) (plan : X → ℕ → Set X → X × List X)
    (init : WalkState X) {a b : ℕ} (hab : a ≤ b) :
    (walkRun U v plan init a).j ≤ (walkRun U v plan init b).j := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction c with
  | zero => exact le_refl _
  | succ c ih =>
    have h1 : (walkRun U v plan init (a + c)).j ≤ (walkRun U v plan init (a + c + 1)).j := by
      have h := walkStep_j_le U v plan (walkRun U v plan init (a + c))
      have he : walkRun U v plan init (a + c + 1)
          = walkStep U v plan (walkRun U v plan init (a + c)) := rfl
      rw [← he] at h
      exact h
    have h2 : (walkRun U v plan init (a + c + 1)).j
        = (walkRun U v plan init (a + (c + 1))).j := rfl
    exact le_trans (le_trans ih h1) (le_of_eq h2)


end Machinery

/-- A walk to infinity with containers: on a connected, second countable, non-compact `ℂ`-charted
surface there is an injective sequence `a` starting at `z₀`, container indices `ctr i → ∞`, a
locally finite family `U` of open coordinate balls (centres `c₀`, radii `r₀ > 0`, closed model balls
inside the chart targets) such that `a i` and `a (i+1)` both lie in `U (ctr i)` and the step is
smaller than one eighth of the distance from the coordinate of `a i` to the boundary of the model
ball of radius `r₀ (ctr i)`.

Route: take `U` from `exists_locallyFinite_openCoordinateBall_cover` with centres `c₀` and radii
`r₀`; take the nerve walk `v` from `exists_nerve_escaping_walk` (which needs the nerve graph to be
connected and locally finite: the `U n` are open, nonempty, have compact closures, cover `X` and are
locally finite); then run the state machine with states `(pt, rem, ctr, j, forb)`: a state with
`rem = y :: t` pops `y` (adding `pt` to `forb`); a state with `rem = []` uses `exists_phase_plan`
with the container `v j` and forbidden set `forb` to obtain a list starting at `pt` and ending at a
point of `U (v j) ∩ U (v (j+1))`, then moves to the second element of that list and sets
`ctr := v j`, `j := j + 1`.  The invariants: the current point and the remaining list avoid `forb`,
all the current list's points lie in `U ctr`, the list is a `FineChain` for the chart of `ctr`, and
every previously emitted point lies in the current `forb` (whence injectivity, since the current
point never lies in `forb`).  `ctr → ∞` because `j` grows by one at each generation and every list
is finite. -/
theorem exists_walk_data {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (z₀ : X) :
    ∃ (a : ℕ → X) (ctr : ℕ → ℕ) (U : ℕ → Set X) (c₀ : ℕ → X) (r₀ : ℕ → ℝ),
      a 0 = z₀ ∧ Function.Injective a ∧ (∀ n, 0 < r₀ n) ∧
      (∀ n, Metric.closedBall ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) ⊆ (chartAt ℂ (c₀ n)).target) ∧
      (∀ n, U n = (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n)) ∧
      LocallyFinite U ∧ Filter.Tendsto ctr Filter.atTop Filter.atTop ∧
      (∀ i, a i ∈ U (ctr i) ∧ a (i + 1) ∈ U (ctr i)) ∧
      (∀ i, dist ((chartAt ℂ (c₀ (ctr i))) (a (i + 1))) ((chartAt ℂ (c₀ (ctr i))) (a i)) <
        (r₀ (ctr i) - dist ((chartAt ℂ (c₀ (ctr i))) (a i))
          ((chartAt ℂ (c₀ (ctr i))) (c₀ (ctr i)))) / 8) := by
  classical
  obtain ⟨c₀, r₀, hrpos, hroom, hopen, hcov, hlf⟩ :=
    exists_locallyFinite_openCoordinateBall_cover (X := X) hX
  let U : ℕ → Set X := fun n =>
    (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n)
  have hUdef : ∀ n, U n =
      (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) := fun n => rfl
  have hUo : ∀ n, IsOpen (U n) := fun n => hopen n
  have hcovU : (⋃ n, U n) = Set.univ := hcov
  have hlfU : LocallyFinite U := hlf
  have hne : ∀ n, (U n).Nonempty := fun n =>
    ⟨c₀ n, (chartAt ℂ (c₀ n)) (c₀ n), Metric.mem_ball_self (hrpos n),
      (chartAt ℂ (c₀ n)).left_inv (mem_chart_source ℂ (c₀ n))⟩
  have hclU : ∀ n, IsCompact (closure (U n)) := by
    intro n
    have hcomp : IsCompact ((chartAt ℂ (c₀ n)).symm ''
        Metric.closedBall ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n)) :=
      Commons.Topology.Surface.isCompact_symm_image_closedBall_chart (c₀ n) (hroom n)
    refine hcomp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcomp.isClosed)
    rintro z ⟨w, hw, hwz⟩
    exact ⟨w, Metric.ball_subset_closedBall hw, hwz⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n, z₀ ∈ U n := by
    have h : z₀ ∈ (⋃ n, U n) := by rw [hcovU]; exact Set.mem_univ z₀
    exact Set.mem_iUnion.mp h
  obtain ⟨v, hv0, hadj, hvlim⟩ :=
    exists_nerve_escaping_walk (X := X) hX hne hUo hcovU hlfU hclU n₀
  let plan : X → ℕ → Set X → X × List X := mkPlan U c₀ r₀ v hUo hUdef hroom hadj
  have hplan : IsGoodPlan U c₀ r₀ v plan := mkPlan_spec U c₀ r₀ v hUo hUdef hroom hadj
  let init : WalkState X := ⟨z₀, [], 0, (∅ : Set X)⟩
  have hinit : WalkInv U c₀ r₀ v init :=
    walkInv_init (U := U) (c₀ := c₀) (r₀ := r₀) (v := v) (z₀ := z₀) (n₀ := n₀) hv0 hn₀
  have hinv : ∀ n, WalkInv U c₀ r₀ v (walkRun U v plan init n) := by
    intro n
    induction n with
    | zero => exact hinit
    | succ n ih =>
      rw [show walkRun U v plan init (n + 1) = walkStep U v plan (walkRun U v plan init n) from rfl]
      exact walkInv_step hplan _ ih
  have hstepF : ∀ n, (walkRun U v plan init (n + 1)).pt ∈ U (v (walkRun U v plan init n).j) ∧
      (walkRun U v plan init (n + 1)).pt ∉ (walkRun U v plan init n).forb ∧
      (walkRun U v plan init (n + 1)).pt ≠ (walkRun U v plan init n).pt ∧
      dist ((chartAt ℂ (c₀ (v (walkRun U v plan init n).j))) (walkRun U v plan init (n + 1)).pt)
        ((chartAt ℂ (c₀ (v (walkRun U v plan init n).j))) (walkRun U v plan init n).pt) <
        (r₀ (v (walkRun U v plan init n).j) -
          dist ((chartAt ℂ (c₀ (v (walkRun U v plan init n).j))) (walkRun U v plan init n).pt)
            ((chartAt ℂ (c₀ (v (walkRun U v plan init n).j)))
              (c₀ (v (walkRun U v plan init n).j)))) / 8 := by
    intro n
    have h := walkStep_step_facts hplan (walkRun U v plan init n) (hinv n)
    rwa [show walkRun U v plan init (n + 1) = walkStep U v plan (walkRun U v plan init n)
      from rfl]
  have hforbF : ∀ n, (walkRun U v plan init (n + 1)).forb =
      insert (walkRun U v plan init n).pt (walkRun U v plan init n).forb := by
    intro n
    have h := walkStep_forb hplan (walkRun U v plan init n) (hinv n)
    rwa [show walkRun U v plan init (n + 1) = walkStep U v plan (walkRun U v plan init n)
      from rfl]
  have hK : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → (walkRun U v plan init m).pt ∈
      Set.insert (walkRun U v plan init n).pt (walkRun U v plan init n).forb := by
    intro n
    induction n with
    | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    | succ n ih =>
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with hlt | heq
      · have h1 := ih m (Nat.lt_succ_iff.mp hlt)
        rw [hforbF n]
        exact Set.mem_insert_of_mem _ h1
      · rw [heq]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hinj : Function.Injective (fun i => (walkRun U v plan init i).pt) := by
    have key : ∀ i j : ℕ, i < j →
        (walkRun U v plan init i).pt ≠ (walkRun U v plan init j).pt := by
      intro i j hij
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hstep := hstepF j'
      have hmem : (walkRun U v plan init i).pt ∈
          Set.insert (walkRun U v plan init j').pt (walkRun U v plan init j').forb :=
        hK j' i (by omega)
      intro hEq
      rw [hEq] at hmem
      rcases Set.mem_insert_iff.mp hmem with h | h
      · exact hstep.2.2.1 h
      · exact hstep.2.1 h
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (key i j h)
    · exact h
    · exact absurd hij.symm (key j i h)
  have hadv : ∀ n, ∃ k : ℕ, 1 ≤ k ∧
      (walkRun U v plan init n).j + 1 ≤ (walkRun U v plan init (n + k)).j := by
    intro n
    obtain ⟨k, hk1, hk2⟩ := j_advance_eventually hplan (walkRun U v plan init n) (hinv n)
    refine ⟨k, hk1, ?_⟩
    rw [← walkRun_add U v plan init n k] at hk2
    exact hk2
  let T : ℕ → ℕ := fun m => Nat.rec 0 (fun n prev => prev + Classical.choose (hadv prev)) m
  have hTsucc : ∀ m, T (m + 1) = T m + Classical.choose (hadv (T m)) := fun m => rfl
  have hTj : ∀ m, m ≤ (walkRun U v plan init (T m)).j := by
    intro m
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih =>
      have hc := (Classical.choose_spec (hadv (T m))).2
      rw [hTsucc m]
      exact le_trans (Nat.succ_le_succ ih) hc
  have hTmono : ∀ m, T m ≤ T (m + 1) := by
    intro m
    rw [hTsucc m]
    exact Nat.le_add_right _ _
  have hctr : Filter.Tendsto (fun i => v ((walkRun U v plan init i).j))
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro M
    obtain ⟨K, hKv⟩ := hvlim M
    refine ⟨T K, fun i hi => ?_⟩
    exact hKv _ (le_trans (hTj K) (walkRun_j_mono U v plan init hi))
  refine ⟨fun i => (walkRun U v plan init i).pt, fun i => v ((walkRun U v plan init i).j),
    U, c₀, r₀, rfl, hinj, hrpos, hroom, hUdef, hlfU, hctr, ?_, ?_⟩
  · intro i
    exact ⟨(hinv i).pt_mem, (hstepF i).1⟩
  · intro i
    exact (hstepF i).2.2.2

end Work.Drive
