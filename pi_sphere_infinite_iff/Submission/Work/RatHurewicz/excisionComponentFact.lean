import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.ThomBordism.TwoSet.Subdivision

/-!
# Reachability inside the pieces of an open cover

Let `X = B ∪ C` with `B`, `C` open and `x₀ ∈ B ∩ C`, and suppose that the points of `B ∩ C` that are
reachable from `x₀` inside `B` (resp. `C`) lie in the path component of `x₀` in `B ∩ C` (the
hypotheses `hBpc`, `hCpc` below; they are the `π₀` content of the vanishing of the relative groups
of the pair, see `hBpc_of_subsingleton` / `hCpc_of_subsingleton`).  Then along any path in `X`
starting at `x₀` one meets only "good" points: points of `B` reachable inside `B` from a point of
`B ∩ C` joined to `x₀` inside `B ∩ C`, or the same with `B` replaced by `C`.

This is the reduction of tom Dieck's Problem 1 after (6.4.1); it is what makes the single-basepoint
hypotheses of `Work.RatHurewicz.excisionRelPiVanishing` usable by the triad compression theorem
`Work.RatHurewicz.triadCompression` (whose hypotheses `hB0`, `hC0` and restricted boundary sets are
consequences of it).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)}

/-- `z` is reachable inside `B` from a point of `B ∩ C` that is joined to `x₀` inside `B ∩ C`. -/
def ReachB (x₀ : ↥(B ∩ C)) (z : X) : Prop :=
  ∃ (q : ↥(B ∩ C)), Nonempty (Path x₀ q) ∧
    ∃ (hz : z ∈ B), Nonempty (Path (interInclLeft B C q) (⟨z, hz⟩ : ↥B))

/-- `z` is reachable inside `C` from a point of `B ∩ C` that is joined to `x₀` inside `B ∩ C`. -/
def ReachC (x₀ : ↥(B ∩ C)) (z : X) : Prop :=
  ∃ (q : ↥(B ∩ C)), Nonempty (Path x₀ q) ∧
    ∃ (hz : z ∈ C), Nonempty (Path (interInclRight B C q) (⟨z, hz⟩ : ↥C))

/-- The good points of a path through the triad. -/
def GoodPt (x₀ : ↥(B ∩ C)) (z : X) : Prop := (z ∈ B ∧ ReachB x₀ z) ∨ (z ∈ C ∧ ReachC x₀ z)

theorem goodPt_base (x₀ : ↥(B ∩ C)) : GoodPt x₀ (x₀ : X) :=
  Or.inl ⟨x₀.2.1, x₀, ⟨Path.refl x₀⟩, x₀.2.1, ⟨Path.refl _⟩⟩

/-- Transport of good-ness along an equality of the underlying point. -/
theorem GoodPt_congr {z z' : X} (h : z = z') (hg : GoodPt x₀ z) : GoodPt x₀ z' := h ▸ hg

/-- A good point lies in `B` or in `C`. -/
theorem GoodPt.mem_or {z : X} (h : GoodPt x₀ z) : z ∈ B ∨ z ∈ C := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- A point of `B ∩ C` reached from `x₀` inside `C` from a point of `B ∩ C` joined to `x₀` is
joined to `x₀` inside `B ∩ C` (this is the `π₀` content of the hypothesis `hCpc`). -/
theorem goodPt_path_of_reachC (hCpc : ∀ a : ↥(B ∩ C),
      Nonempty (Path (interInclRight B C x₀) (interInclRight B C a)) → Nonempty (Path x₀ a))
    {z : X} (hz : z ∈ B ∩ C) (h : ReachC x₀ z) : Nonempty (Path x₀ ⟨z, hz⟩) := by
  rcases h with ⟨q, hq, hzC, ⟨δ⟩⟩
  refine hCpc ⟨z, hz⟩ ⟨?_⟩
  exact ((hq.some.map (interInclRight B C).continuous).trans (δ.cast rfl (Subtype.ext rfl))).cast
    rfl (Subtype.ext rfl)

/-- A point of `B ∩ C` reached from `x₀` inside `B` from a point of `B ∩ C` joined to `x₀` is
joined to `x₀` inside `B ∩ C` (this is the `π₀` content of the hypothesis `hBpc`). -/
theorem goodPt_path_of_reachB (hBpc : ∀ a : ↥(B ∩ C),
      Nonempty (Path (interInclLeft B C x₀) (interInclLeft B C a)) → Nonempty (Path x₀ a))
    {z : X} (hz : z ∈ B ∩ C) (h : ReachB x₀ z) : Nonempty (Path x₀ ⟨z, hz⟩) := by
  rcases h with ⟨q, hq, hzB, ⟨δ⟩⟩
  refine hBpc ⟨z, hz⟩ ⟨?_⟩
  exact ((hq.some.map (interInclLeft B C).continuous).trans (δ.cast rfl (Subtype.ext rfl))).cast
    rfl (Subtype.ext rfl)

/-- **Propagation of good-ness along a leg contained in `B`.** -/
theorem goodPt_of_leg_B (hCpc : ∀ a : ↥(B ∩ C),
      Nonempty (Path (interInclRight B C x₀) (interInclRight B C a)) → Nonempty (Path x₀ a))
    {a b : X} (ha : GoodPt x₀ a) (haB : a ∈ B) (hbB : b ∈ B)
    (δ : Path (⟨a, haB⟩ : ↥B) (⟨b, hbB⟩ : ↥B)) : GoodPt x₀ b := by
  cases ha with
  | inl h =>
    obtain ⟨-, hrest⟩ := h
    obtain ⟨q, hq, hzB, hpath⟩ := hrest
    rcases hpath with ⟨δ'⟩
    refine Or.inl ⟨hbB, q, hq, hbB, ⟨?_⟩⟩
    exact ((δ'.cast rfl (Subtype.ext rfl)).trans δ).cast rfl (Subtype.ext rfl)
  | inr h =>
    obtain ⟨haC, hrest⟩ := h
    obtain ⟨q, hq, hzC, hpath⟩ := hrest
    rcases hpath with ⟨δ'⟩
    have hamem : a ∈ B ∩ C := ⟨haB, haC⟩
    have hjoin : Nonempty (Path x₀ ⟨a, hamem⟩) :=
      goodPt_path_of_reachC (x₀ := x₀) hCpc hamem ⟨q, hq, haC, ⟨δ'⟩⟩
    refine Or.inl ⟨hbB, ⟨a, hamem⟩, hjoin, hbB, ⟨?_⟩⟩
    exact ((Path.refl (⟨a, haB⟩ : ↥B)).trans δ).cast rfl (Subtype.ext rfl)

/-- **Propagation of good-ness along a leg contained in `C`.** -/
theorem goodPt_of_leg_C (hBpc : ∀ a : ↥(B ∩ C),
      Nonempty (Path (interInclLeft B C x₀) (interInclLeft B C a)) → Nonempty (Path x₀ a))
    {a b : X} (ha : GoodPt x₀ a) (haC : a ∈ C) (hbC : b ∈ C)
    (δ : Path (⟨a, haC⟩ : ↥C) (⟨b, hbC⟩ : ↥C)) : GoodPt x₀ b := by
  cases ha with
  | inl h =>
    obtain ⟨haB, hrest⟩ := h
    obtain ⟨q, hq, hzB, hpath⟩ := hrest
    rcases hpath with ⟨δ'⟩
    have hamem : a ∈ B ∩ C := ⟨haB, haC⟩
    have hjoin : Nonempty (Path x₀ ⟨a, hamem⟩) :=
      goodPt_path_of_reachB (x₀ := x₀) hBpc hamem ⟨q, hq, haB, ⟨δ'⟩⟩
    refine Or.inr ⟨hbC, ⟨a, hamem⟩, hjoin, hbC, ⟨?_⟩⟩
    exact ((Path.refl (⟨a, haC⟩ : ↥C)).trans δ).cast rfl (Subtype.ext rfl)
  | inr h =>
    obtain ⟨-, hrest⟩ := h
    obtain ⟨q, hq, hzC, hpath⟩ := hrest
    rcases hpath with ⟨δ'⟩
    refine Or.inr ⟨hbC, q, hq, hbC, ⟨?_⟩⟩
    exact ((δ'.cast rfl (Subtype.ext rfl)).trans δ).cast rfl (Subtype.ext rfl)

/-! ## The `π₀` content of the vanishing of the relative groups

The hypotheses `hBpc`, `hCpc` of `exists_path_in_inter_of_mem_pathComponent` are consequences of the
vanishing of `RelHomotopyGroup (interInclLeft B C) x₀ 0` (the `π₀` of the homotopy fibre
`F_B`): a path in `↥B` between `interInclLeft x₀` and `interInclLeft a` is a point of `F_B`, and
paths in `F_B` project to paths in `↥(B ∩ C)`. -/

/-- The `π₀`-part of the vanishing at `x₀` of the relative groups of `(B, B ∩ C)`. -/
theorem hBpc_of_subsingleton (h0 : Subsingleton (RelHomotopyGroup (interInclLeft B C) x₀ 0)) :
    ∀ a : ↥(B ∩ C), Nonempty (Path (interInclLeft B C x₀) (interInclLeft B C a)) →
      Nonempty (Path x₀ a) := by
  rintro a ⟨γ⟩
  haveI : PathConnectedSpace (homotopyFibre (interInclLeft B C) x₀) :=
    pathConnectedSpace_of_subsingleton_pi_zero (homotopyFibreBasepoint (interInclLeft B C) x₀) h0
  let p : homotopyFibre (interInclLeft B C) x₀ :=
    ⟨(a, ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩
  obtain ⟨δ⟩ := PathConnectedSpace.joined p (homotopyFibreBasepoint (interInclLeft B C) x₀)
  exact ⟨(δ.map (homotopyFibreFst (interInclLeft B C) x₀).continuous).symm⟩

/-- The `π₀`-part of the vanishing at `x₀` of the relative groups of `(C, B ∩ C)`. -/
theorem hCpc_of_subsingleton (h0 : Subsingleton (RelHomotopyGroup (interInclRight B C) x₀ 0)) :
    ∀ a : ↥(B ∩ C), Nonempty (Path (interInclRight B C x₀) (interInclRight B C a)) →
      Nonempty (Path x₀ a) := by
  rintro a ⟨γ⟩
  haveI : PathConnectedSpace (homotopyFibre (interInclRight B C) x₀) :=
    pathConnectedSpace_of_subsingleton_pi_zero (homotopyFibreBasepoint (interInclRight B C) x₀) h0
  let p : homotopyFibre (interInclRight B C) x₀ :=
    ⟨(a, ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩
  obtain ⟨δ⟩ := PathConnectedSpace.joined p (homotopyFibreBasepoint (interInclRight B C) x₀)
  exact ⟨(δ.map (homotopyFibreFst (interInclRight B C) x₀).continuous).symm⟩

/-! ## The linear parametrisation of a leg of the interval -/

theorem legPt_mem_I (a b s : I) :
    0 ≤ (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) ∧
      (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) ≤ 1 := by
  have h1 : (0 : ℝ) ≤ (a : ℝ) := a.2.1
  have h2 : (a : ℝ) ≤ 1 := a.2.2
  have h3 : (0 : ℝ) ≤ (b : ℝ) := b.2.1
  have h4 : (b : ℝ) ≤ 1 := b.2.2
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  constructor <;> nlinarith

/-- The linear parametrisation of the segment `[a, b]` of the interval, `s ↦ (1-s)a + sb`. -/
def legPt (a b : I) (s : I) : I :=
  ⟨(1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ), legPt_mem_I a b s⟩

theorem legPt_coe (a b s : I) :
    (legPt a b s : ℝ) = (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) := rfl

theorem continuous_legPt (a b : I) : Continuous (legPt a b) :=
  Continuous.subtype_mk
    (f := fun s : I => (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ))
    (by fun_prop) (legPt_mem_I a b)

@[simp] theorem legPt_zero (a b : I) : legPt a b 0 = a := by
  apply Subtype.ext
  rw [legPt_coe]
  norm_num

@[simp] theorem legPt_one (a b : I) : legPt a b 1 = b := by
  apply Subtype.ext
  rw [legPt_coe]
  norm_num

/-- The parametrised segment stays between its endpoints. -/
theorem legPt_mem {a b : I} (hab : a ≤ b) (s : I) :
    a ≤ legPt a b s ∧ legPt a b s ≤ b := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := Subtype.coe_le_coe.mpr hab
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  constructor
  · rw [← Subtype.coe_le_coe, legPt_coe]; nlinarith
  · rw [← Subtype.coe_le_coe, legPt_coe]; nlinarith

/-- **The reduction of tom Dieck's Problem 1 after (6.4.1).**  Under the hypotheses `hBpc`/`hCpc`,
every point of `pathComponent x₀` is either reachable inside `B` from `B ∩ C` or inside `C` from
`B ∩ C`, and every point of `B ∩ C` in that component is joined to `x₀` inside `B ∩ C`. -/
theorem exists_path_in_inter_of_mem_pathComponent (hB : IsOpen B) (hC : IsOpen C)
    (hBC : B ∪ C = Set.univ) (x₀ : ↥(B ∩ C))
    (hBpc : ∀ a : ↥(B ∩ C),
      Nonempty (Path (interInclLeft B C x₀) (interInclLeft B C a)) → Nonempty (Path x₀ a))
    (hCpc : ∀ a : ↥(B ∩ C),
      Nonempty (Path (interInclRight B C x₀) (interInclRight B C a)) → Nonempty (Path x₀ a))
    {y : X} (hy : y ∈ pathComponent (x₀ : X)) :
    (∀ (hyB : y ∈ B), ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.1⟩ (⟨y, hyB⟩ : ↥B)))
    ∧ (∀ (hyC : y ∈ C), ∃ a : ↥(B ∩ C), Nonempty (Path ⟨a.1, a.2.2⟩ (⟨y, hyC⟩ : ↥C)))
    ∧ (∀ (hyBC : y ∈ B ∩ C), Nonempty (Path x₀ (⟨y, hyBC⟩ : ↥(B ∩ C)))) := by
  classical
  obtain ⟨γ⟩ : Nonempty (Path (x₀ : X) y) := mem_pathComponent_iff.mp hy
  -- the Lebesgue subdivision of the interval for the cover `{B, C}`
  obtain ⟨N, hN, hgrid⟩ := Work.ThomBordism.TwoSet.Subdivision (U := B) (V := C) hB hC hBC
    (j := 1) ⟨fun z : Work.ThomBordism.TwoSet.IC 1 => γ (z 0),
      γ.toContinuousMap.continuous.comp (by fun_prop)⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- the grid points
  let τ : ℕ → I := fun i => ⟨min 1 ((i : ℝ) / N),
    le_min (by norm_num) (div_nonneg (Nat.cast_nonneg i) hNpos.le), min_le_left _ _⟩
  have hτle : ∀ i, i ≤ N → (τ i : ℝ) = (i : ℝ) / N := by
    intro i hi
    show min 1 ((i : ℝ) / N) = (i : ℝ) / N
    exact min_eq_right (by rw [div_le_one hNpos]; exact_mod_cast hi)
  have hτmono : ∀ i, i < N → τ i ≤ τ (i + 1) := by
    intro i hi
    rw [← Subtype.coe_le_coe, hτle i (le_of_lt hi), hτle (i + 1) hi]
    push_cast
    rw [add_div]
    exact le_add_of_nonneg_right (by positivity)
  -- the box condition for a leg
  have mem_box : ∀ i, i < N → ∀ s : I, τ i ≤ s → s ≤ τ (i + 1) →
      ((i : ℝ) ≤ (N : ℝ) * (s : ℝ) ∧ (N : ℝ) * (s : ℝ) ≤ (i : ℝ) + 1) := by
    intro i hi s hs1 hs2
    have h1 : (i : ℝ) / N ≤ (s : ℝ) := by
      have h := Subtype.coe_le_coe.mpr hs1
      rwa [hτle i (le_of_lt hi)] at h
    have h2 : (s : ℝ) ≤ ((i : ℝ) + 1) / N := by
      have h := Subtype.coe_le_coe.mpr hs2
      rw [hτle (i + 1) hi] at h
      push_cast at h
      exact h
    constructor
    · rw [div_le_iff₀ hNpos] at h1; linarith
    · rw [le_div_iff₀ hNpos] at h2; linarith
  -- every leg lies entirely in `B` or entirely in `C`
  have hleg : ∀ i, i < N → (∀ s : I, τ i ≤ s → s ≤ τ (i + 1) → γ s ∈ B)
      ∨ (∀ s : I, τ i ≤ s → s ≤ τ (i + 1) → γ s ∈ C) := by
    intro i hi
    rcases hgrid (fun _ : Fin 1 => (⟨i, hi⟩ : Fin N)) with h | h
    · left
      intro s hs1 hs2
      exact h (fun _ : Fin 1 => s) (fun j => by
        simpa using mem_box i hi s hs1 hs2)
    · right
      intro s hs1 hs2
      exact h (fun _ : Fin 1 => s) (fun j => by
        simpa using mem_box i hi s hs1 hs2)
  -- the induction along the grid
  have key : ∀ i, i ≤ N → GoodPt x₀ (γ (τ i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 : τ 0 = (0 : I) := by
        apply Subtype.ext
        rw [hτle 0 (Nat.zero_le N)]
        simp
      have hγ0 : γ (τ 0) = (x₀ : X) := by
        rw [h0]
        exact γ.source'
      exact GoodPt_congr hγ0.symm (goodPt_base x₀)
    | succ k ih =>
      intro hk
      have hkN : k < N := Nat.lt_of_succ_le hk
      have hprev : GoodPt x₀ (γ (τ k)) := ih (le_of_lt hkN)
      have hle : τ k ≤ τ (k + 1) := hτmono k hkN
      rcases hleg k hkN with hBleg | hCleg
      · have haB : γ (τ k) ∈ B := hBleg (τ k) le_rfl hle
        have hbB : γ (τ (k + 1)) ∈ B := hBleg (τ (k + 1)) hle le_rfl
        have hmem : ∀ s : I, γ (legPt (τ k) (τ (k + 1)) s) ∈ B := fun s =>
          hBleg _ (legPt_mem hle s).1 (legPt_mem hle s).2
        refine goodPt_of_leg_B (x₀ := x₀) hCpc hprev haB hbB ?_
        refine ⟨⟨fun s => ⟨γ (legPt (τ k) (τ (k + 1)) s), hmem s⟩,
          Continuous.subtype_mk (f := fun s : I => γ (legPt (τ k) (τ (k + 1)) s))
            (γ.toContinuousMap.continuous.comp (continuous_legPt _ _)) hmem⟩, ?_, ?_⟩
        · apply Subtype.ext
          show γ (legPt (τ k) (τ (k + 1)) 0) = γ (τ k)
          rw [legPt_zero]
        · apply Subtype.ext
          show γ (legPt (τ k) (τ (k + 1)) 1) = γ (τ (k + 1))
          rw [legPt_one]
      · have haC : γ (τ k) ∈ C := hCleg (τ k) le_rfl hle
        have hbC : γ (τ (k + 1)) ∈ C := hCleg (τ (k + 1)) hle le_rfl
        have hmem : ∀ s : I, γ (legPt (τ k) (τ (k + 1)) s) ∈ C := fun s =>
          hCleg _ (legPt_mem hle s).1 (legPt_mem hle s).2
        refine goodPt_of_leg_C (x₀ := x₀) hBpc hprev haC hbC ?_
        refine ⟨⟨fun s => ⟨γ (legPt (τ k) (τ (k + 1)) s), hmem s⟩,
          Continuous.subtype_mk (f := fun s : I => γ (legPt (τ k) (τ (k + 1)) s))
            (γ.toContinuousMap.continuous.comp (continuous_legPt _ _)) hmem⟩, ?_, ?_⟩
        · apply Subtype.ext
          show γ (legPt (τ k) (τ (k + 1)) 0) = γ (τ k)
          rw [legPt_zero]
        · apply Subtype.ext
          show γ (legPt (τ k) (τ (k + 1)) 1) = γ (τ (k + 1))
          rw [legPt_one]
  have hτN : τ N = (1 : I) := by
    apply Subtype.ext
    rw [hτle N le_rfl]
    exact div_self (ne_of_gt hNpos)
  have hgood : GoodPt x₀ y := by
    have hγN : γ (τ N) = y := by
      rw [hτN]
      exact γ.target'
    exact GoodPt_congr hγN (key N le_rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro hyB
    have hg := hgood
    rcases hg with ⟨-, q, hq, hzB, ⟨δ⟩⟩ | ⟨hyC, q, hq, -, ⟨δ⟩⟩
    · exact ⟨q, ⟨δ.cast rfl (Subtype.ext rfl)⟩⟩
    · exact ⟨⟨y, hyB, hyC⟩, ⟨Path.refl (⟨y, hyB⟩ : ↥B)⟩⟩
  · intro hyC
    have hg := hgood
    rcases hg with ⟨hyB, q, hq, -, ⟨δ⟩⟩ | ⟨-, q, hq, hzC, ⟨δ⟩⟩
    · exact ⟨⟨y, hyB, hyC⟩, ⟨Path.refl (⟨y, hyC⟩ : ↥C)⟩⟩
    · exact ⟨q, ⟨δ.cast rfl (Subtype.ext rfl)⟩⟩
  · intro hyBC
    have hg := hgood
    rcases hg with ⟨-, q, hq, hzB, ⟨δ⟩⟩ | ⟨-, q, hq, hzC, ⟨δ⟩⟩
    · exact goodPt_path_of_reachB (x₀ := x₀) hBpc hyBC ⟨q, hq, hzB, ⟨δ⟩⟩
    · exact goodPt_path_of_reachC (x₀ := x₀) hCpc hyBC ⟨q, hq, hzC, ⟨δ⟩⟩

end

end Work.RatHurewicz
