import Mathlib
import Submission.Work.Drive.PushDisc.asymAnchor
import Submission.Work.Drive.PushDisc.asymChart
import Submission.Work.Drive.PushDisc.windowChart

/-!
# The `hiso` row of `WhitneyChartWindowData` from a clean model disc

This is the **`hiso` half** of the framing `whitneyChart_of_disc`, split off as its own statement
(project lead, 13:00: "the `hiso` side follows straight from the clean disc plus `discIsolation`").

The row `hiso` of `Work.Drive.PushDisc.WhitneyChartWindowData` reads

    ∃ V open, asymDisc k c ⊆ V ∧ ∀ z, Φ (f z) ∈ V →
      ((Φ (f z)).2.1 = 0 ∧ (Φ (f z)).2.2.2 = 0) ∨ z ∈ σ₂ '' asymReg k X'

i.e. *near the model disc the only preimages come from the plane `{y = 0, v = 0}` (the first sheet)
and from the finger*.  The content splits into two:
* a **decomposition** of `V`: `V` is covered by the plane, by the finger's image, and by the image of
  the *interior* of the model Whitney disc `Dm` (`hVcover`) — this is what the framing's chart
  construction supplies;
* the **cleanliness of the disc**: no point of `M` maps into the disc's interior (`hDclean`) — this is
  `Work.Drive.Whitney.whitneyDiscSmooth`, and it is available axiom-clean
  (`exists_isolation_of_whitneyDisc` in `Drive/PushDisc/discIsolation.lean` is its neighbourhood
  form).

Given those, `hiso` is a pure point-set consequence of `hclean` and the pinning of the two double
points (which puts `f p₁, f p₂, f q₁, f q₂` on the plane): if `Φ (f z)` is not on the plane and not in
the disc's interior, it is the finger's image of some `σ₂ p`, and `hclean` forces `z` to be `σ₂ p`
(the four double-point alternatives all put `Φ (f z)` back on the plane).
-/

namespace Work.Drive.PushDisc

open Set Metric

/-- **The `hiso` row from a clean model disc.**  See the module docstring. -/
theorem hiso_of_modelDisc {k : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ)
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0))
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M) (X' : ℝ)
    (hσ₂W : σ₂ '' asymReg k X' ⊆ W)
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (V : Set (Work.Drive.Whitney.Mdl k))
    (hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W)
    (hVcover : ∀ z : M, Φ (f z) ∈ V →
      Φ (f z) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ (∃ p : ℝ × EuclideanSpace ℝ (Fin k),
          p ∈ asymReg k X' ∧ Φ (f (σ₂ p)) = Φ (f z))
      ∨ Φ (f z) ∈ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1))
    (hDclean : ∀ z : M, Φ (f z) ∉ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ∀ z : M, Φ (f z) ∈ V →
      ((Φ (f z)).2.1 = 0 ∧ (Φ (f z)).2.2.2 = 0) ∨ z ∈ σ₂ '' asymReg k X' := by
  have hP₁ : Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) := by rw [hp₁c, hΦΘ]
  have hP₂ : Φ (f p₂) = ((-1 : ℝ), 0, 0, 0) := by rw [← hfp, hP₁]
  have hQ₁ : Φ (f q₁) = ((1 : ℝ), 0, 0, 0) := by rw [hq₁c, hΦΘ]
  have hQ₂ : Φ (f q₂) = ((1 : ℝ), 0, 0, 0) := by rw [← hfq, hQ₁]
  intro z hz
  by_cases hpl : (Φ (f z)).2.1 = 0 ∧ (Φ (f z)).2.2.2 = 0
  · exact Or.inl hpl
  refine Or.inr ?_
  rcases hVcover z hz with hpl' | hfin | hdisc
  · exact absurd hpl' hpl
  · obtain ⟨p, hp, hpz⟩ := hfin
    have hfz : f (σ₂ p) = f z := by
      have h := congrArg Θ hpz
      simpa only [hΘΦ] using h
    rcases hclean (σ₂ p) z (hσ₂W ⟨p, hp, rfl⟩) (hVW z hz) hfz with h | h | h | h | h
    · exact ⟨p, hp, h⟩
    · exfalso
      have hz' : Φ (f z) = ((-1 : ℝ), 0, 0, 0) := by rw [h.2]; exact hP₂
      exact hpl (by constructor <;> rw [hz'])
    · exfalso
      have hz' : Φ (f z) = ((-1 : ℝ), 0, 0, 0) := by rw [h.2]; exact hP₁
      exact hpl (by constructor <;> rw [hz'])
    · exfalso
      have hz' : Φ (f z) = ((1 : ℝ), 0, 0, 0) := by rw [h.2]; exact hQ₂
      exact hpl (by constructor <;> rw [hz'])
    · exfalso
      have hz' : Φ (f z) = ((1 : ℝ), 0, 0, 0) := by rw [h.2]; exact hQ₁
      exact hpl (by constructor <;> rw [hz'])
  · exact absurd hdisc (hDclean z)

/-- **The `hiso` row of `WhitneyChartWindowData`, in the exact shape of the interface.** -/
theorem exists_hiso_of_modelDisc {k : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ)
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0))
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M) (X' : ℝ)
    (hσ₂W : σ₂ '' asymReg k X' ⊆ W)
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (c : ℝ → ℝ) (V : Set (Work.Drive.Whitney.Mdl k))
    (hVo : IsOpen V) (hVD : asymDisc k c ⊆ V)
    (hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W)
    (hVcover : ∀ z : M, Φ (f z) ∈ V →
      Φ (f z) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ (∃ p : ℝ × EuclideanSpace ℝ (Fin k),
          p ∈ asymReg k X' ∧ Φ (f (σ₂ p)) = Φ (f z))
      ∨ Φ (f z) ∈ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1))
    (hDclean : ∀ z : M, Φ (f z) ∉ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ∃ V' : Set (Work.Drive.Whitney.Mdl k), IsOpen V' ∧ asymDisc k c ⊆ V' ∧
      ∀ z : M, Φ (f z) ∈ V' →
        ((Φ (f z)).2.1 = 0 ∧ (Φ (f z)).2.2.2 = 0) ∨ z ∈ σ₂ '' asymReg k X' :=
  ⟨V, hVo, hVD, hiso_of_modelDisc f Φ Θ hΘΦ hΦΘ W p₁ p₂ q₁ q₂ hfp hfq hclean hp₁c hq₁c σ₂ X'
    hσ₂W Dm V hVW hVcover hDclean⟩

/-- **The cleanliness of the model disc from the cleanliness of the Whitney disc**: if
`Dm = Φ ∘ D` and `D`'s open-region image misses `f '' M`, then no point of `M` maps into `Dm`'s open
region. -/
theorem not_mem_modelDisc_image {k : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΘΦ : ∀ y, Θ (Φ y) = y)
    (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * (k + 1)))) (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hDm : ∀ p : ℝ × ℝ, Dm p = Φ (D p))
    (hDclean : ∀ z : M, f z ∉ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ∀ z : M, Φ (f z) ∉ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  obtain ⟨p, hp, hpeq⟩ := hz
  have h1 : Φ (f z) = Φ (D p) := by rw [← hpeq, hDm]
  have h2 : f z = D p := by
    have h := congrArg Θ h1
    simpa only [hΘΦ] using h
  exact hDclean z ⟨p, hp, h2.symm⟩


/-! ## The `hiso` half assembled into the interface

`nonempty_windowChartData_of_rows` takes **every row of `WhitneyChartWindowData` except `hiso`**
(which the framing constructs: the coordinates, the first-sheet pinning, the finger as a graph, the
core height with its sign pattern and the frontier row) together with the three geometric inputs of
the `hiso` half — the decomposition `hVcover` of a neighbourhood `V` of `asymDisc k c` into the plane,
the finger and the model disc's interior, the membership `hVW` of the preimages of `V` in the clean
region `W`, and the cleanliness `hDclean` of the model disc — and produces the whole structure.  So
the *only* geometric input the framing now owes for `hiso` is `hVcover` (and `hDclean`, which is the
Whitney disc's cleanliness, available axiom-clean). -/

theorem nonempty_windowChartData_of_rows {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (k : ℕ) (hk : n = k + 1) (X' : ℝ) (hX' : 1 < X')
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ)
    (h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X'))
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M)
    (hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2))
    (hp₂ : σ₂ ((-1 : ℝ), 0) = p₂) (hq₂ : σ₂ ((1 : ℝ), 0) = q₂)
    (hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X''))
    (hW₀W : σ₂ '' asymReg k X' ⊆ W)
    (c : ℝ → ℝ) (hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0))
    (hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X',
      ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖)
    (hcm : c (-1) = 0) (hc1 : c 1 = 0)
    (hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x)
    (hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0)
    (hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
      ∀ x ∈ frontier (σ₂ '' asymReg k X''),
        |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1)
    (hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0))
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (V : Set (Work.Drive.Whitney.Mdl k)) (hVo : IsOpen V) (hVD : asymDisc k c ⊆ V)
    (hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W)
    (hVcover : ∀ z : M, Φ (f z) ∈ V →
      Φ (f z) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ (∃ p : ℝ × EuclideanSpace ℝ (Fin k),
          p ∈ asymReg k X' ∧ Φ (f (σ₂ p)) = Φ (f z))
      ∨ Φ (f z) ∈ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1))
    (hDclean : ∀ z : M, Φ (f z) ∉ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)) :
    Nonempty (WhitneyChartWindowData n f W p₁ p₂ q₁ q₂) := by
  subst hk
  exact ⟨k, rfl, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, h, hh, σ₂, hσ₂, hp₂, hq₂, hW₀o, hW₀W,
    c, hcsm, hcore, hlip, hcm, hc1, hcpos, hcneg, hfrontier,
    ⟨V, hVo, hVD, fun z hz =>
      hiso_of_modelDisc f Φ Θ hΘΦ hΦΘ W p₁ p₂ q₁ q₂ hfp hfq hclean hp₁c hq₁c σ₂ X'
        hW₀W Dm V hVW hVcover hDclean z hz⟩, hp₁c, hq₁c⟩


/-! ## The cover `hVcover`: the last geometric row of the `hiso` half

`hVcover` says that a neighbourhood `V` of the model disc `asymDisc k c`, whose preimages lie in the
clean region `W`, is covered by the plane `{y = 0, v = 0}`, by the finger and by the **interior** of
the model Whitney disc `Dm`.  Splitting it this way makes the two halves independent:

* the *interior* part is the disc's cleanliness (`hDclean`, free from `whitneyDiscSmooth` via
  `not_mem_modelDisc_image`);
* the *boundary* part is the disc's boundary structure, which for `Dm = Φ ∘ D` and the Whitney disc
  `D` is: `D (·,0)` is the `γ₁`-arc (hence lands in the plane, the first sheet being flat) and
  `D (·,1)` is the `γ₂`-arc (hence lands on the finger); at `x = ±1` the disc is constant at the
  double values, which lie on the plane.

So `hVcover` follows from two rows — the inclusion `hVsub` of `V` into plane ∪ finger ∪ `Dm ''` of
the *closed* square, and the boundary row `hbdry` — and `nonempty_windowChartData_of_disc` below
assembles the whole structure from the chart rows plus the disc. -/

/-- The boundary of the closed square `[-1,1] × [0,1]` is the union of its four sides. -/
theorem boundary_square {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hpi : p ∉ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) :
    p.1 = -1 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1a, h1b, h2a, h2b⟩ := hcon
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
  obtain ⟨hp1lo, hp1hi⟩ := Set.mem_Icc.mp hp1
  obtain ⟨hp2lo, hp2hi⟩ := Set.mem_Icc.mp hp2
  refine hpi ⟨?_, ?_⟩
  · rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne hp1lo (Ne.symm h1a), lt_of_le_of_ne hp1hi h1b⟩
  · rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne hp2lo (Ne.symm h2a), lt_of_le_of_ne hp2hi h2b⟩

/-- **The cover `hVcover` from the boundary of the disc.**  If the neighbourhood `V` is covered by the
plane, the finger and the image of the *closed* square, and the *boundary* of the square maps into the
plane or the finger, then `V` is covered with the image of the **open** square in place of the closed
one — which is `hVcover`. -/
theorem mem_cover_of_modelDisc {k : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M) (X' : ℝ)
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (V : Set (Work.Drive.Whitney.Mdl k))
    (hVsub : ∀ z : M, Φ (f z) ∈ V →
      Φ (f z) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ (∃ q : ℝ × EuclideanSpace ℝ (Fin k),
          q ∈ asymReg k X' ∧ Φ (f (σ₂ q)) = Φ (f z))
      ∨ Φ (f z) ∈ Dm '' (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hbdry : ∀ p : ℝ × ℝ, p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      p ∉ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 →
      Dm p ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ ∃ q : ℝ × EuclideanSpace ℝ (Fin k),
          q ∈ asymReg k X' ∧ Φ (f (σ₂ q)) = Dm p) :
    ∀ z : M, Φ (f z) ∈ V →
      Φ (f z) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ (∃ q : ℝ × EuclideanSpace ℝ (Fin k),
          q ∈ asymReg k X' ∧ Φ (f (σ₂ q)) = Φ (f z))
      ∨ Φ (f z) ∈ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  rcases hVsub z hz with hpl | hfing | hdisc
  · exact Or.inl hpl
  · exact Or.inr (Or.inl hfing)
  · obtain ⟨p, hp, hpeq⟩ := hdisc
    by_cases hpi : p ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1
    · exact Or.inr (Or.inr ⟨p, hpi, hpeq⟩)
    · rcases hbdry p hp hpi with hb | hb
      · exact Or.inl (by rw [← hpeq]; exact hb)
      · obtain ⟨q, hq, hqe⟩ := hb
        exact Or.inr (Or.inl ⟨q, hq, hqe.trans hpeq⟩)

/-- **The whole chart from the chart rows plus the Whitney disc.**  This is the `hiso` half complete:
all the rows of `WhitneyChartWindowData` except `hiso`, the model disc `Dm = Φ ∘ D` of the **smooth
Whitney disc** `D` (which supplies the cleanliness `hDclean`), the two cover rows (`hVsub` and
`hbdry`) and the smallness row `hVW`, produce the whole structure. -/
theorem nonempty_windowChartData_of_disc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (k : ℕ) (hk : n = k + 1) (X' : ℝ) (hX' : 1 < X')
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ)
    (h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X'))
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M)
    (hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2))
    (hp₂ : σ₂ ((-1 : ℝ), 0) = p₂) (hq₂ : σ₂ ((1 : ℝ), 0) = q₂)
    (hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X''))
    (hW₀W : σ₂ '' asymReg k X' ⊆ W)
    (c : ℝ → ℝ) (hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0))
    (hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X',
      ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖)
    (hcm : c (-1) = 0) (hc1 : c 1 = 0)
    (hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x)
    (hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0)
    (hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
      ∀ x ∈ frontier (σ₂ '' asymReg k X''),
        |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1)
    (hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0))
    (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * (n))))
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (hDm : ∀ p : ℝ × ℝ, Dm p = Φ (D p))
    (hDclean : ∀ z : M, f z ∉ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1))
    (V : Set (Work.Drive.Whitney.Mdl k)) (hVo : IsOpen V) (hVD : asymDisc k c ⊆ V)
    (hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W)
    (hVsub : ∀ z : M, Φ (f z) ∈ V →
      Φ (f z) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ (∃ q : ℝ × EuclideanSpace ℝ (Fin k),
          q ∈ asymReg k X' ∧ Φ (f (σ₂ q)) = Φ (f z))
      ∨ Φ (f z) ∈ Dm '' (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hbdry : ∀ p : ℝ × ℝ, p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      p ∉ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 →
      Dm p ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ ∃ q : ℝ × EuclideanSpace ℝ (Fin k),
          q ∈ asymReg k X' ∧ Φ (f (σ₂ q)) = Dm p) :
    Nonempty (WhitneyChartWindowData n f W p₁ p₂ q₁ q₂) := by
  subst hk
  refine nonempty_windowChartData_of_rows f W p₁ p₂ q₁ q₂ hfp hfq hclean k rfl X' hX' Φ Θ hΦsm
    hΘsm hΘΦ hΦΘ h hh σ₂ hσ₂ hp₂ hq₂ hW₀o hW₀W c hcsm hcore hlip hcm hc1 hcpos hcneg hfrontier
    hp₁c hq₁c Dm V hVo hVD hVW ?_ ?_
  · exact mem_cover_of_modelDisc f Φ σ₂ X' Dm V hVsub hbdry
  · exact not_mem_modelDisc_image f Φ Θ hΘΦ D Dm hDm hDclean


/-- **The boundary row `hbdry` of the cover, from the Whitney disc's boundary.**  The rows are those of
`Work.Drive.Whitney.whitneyDiscSmooth` (`D (·,0) = f ∘ γ₁`, `D (·,1) = f ∘ γ₂`, the two ends constant
at the double values) together with the chart rows: the first sheet's arc maps into the plane
`sheetA` (this is the flattening) and the finger's window parametrises the `γ₂`-arc. -/
theorem bdry_of_whitneyDisc {k : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (γ₁ γ₂ : ℝ → M) (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M) (X' : ℝ)
    (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (hDm : ∀ p : ℝ × ℝ, Dm p = Φ (D p))
    (hDbot : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 0) = f (γ₁ ((x + 1) / 2)))
    (hDtop : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 1) = f (γ₂ ((x + 1) / 2)))
    (hDleft : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D (-1, t) = f (γ₁ 0))
    (hDright : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D (1, t) = f (γ₁ 1))
    (hflat : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      Φ (f (γ₁ s)) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0})
    (harc : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∃ q : ℝ × EuclideanSpace ℝ (Fin k), q ∈ asymReg k X' ∧ σ₂ q = γ₂ s) :
    ∀ p : ℝ × ℝ, p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      p ∉ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 →
      Dm p ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ ∃ q : ℝ × EuclideanSpace ℝ (Fin k),
          q ∈ asymReg k X' ∧ Φ (f (σ₂ q)) = Dm p := by
  rintro ⟨a, b⟩ hp hpi
  have hp1 : a ∈ Set.Icc (-1 : ℝ) 1 := (Set.mem_prod.mp hp).1
  have hp2 : b ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
  obtain ⟨hp1lo, hp1hi⟩ := Set.mem_Icc.mp hp1
  have hs : (a + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.mem_Icc]; constructor <;> linarith
  rcases boundary_square hp hpi with h | h | h | h
  · -- the left end: constant at `f p₁`, on the plane
    have ha : a = -1 := h
    left
    rw [hDm, ha, hDleft b hp2]
    exact hflat 0 (by norm_num)
  · -- the right end: constant at `f q₁`, on the plane
    have ha : a = 1 := h
    left
    rw [hDm, ha, hDright b hp2]
    exact hflat 1 (by norm_num)
  · -- the bottom edge: the `γ₁`-arc, on the plane
    have hb : b = 0 := h
    left
    rw [hDm, hb, hDbot a hp1]
    exact hflat ((a + 1) / 2) hs
  · -- the top edge: the `γ₂`-arc, on the finger
    have hb : b = 1 := h
    right
    obtain ⟨q, hq, hqeq⟩ := harc ((a + 1) / 2) hs
    refine ⟨q, hq, ?_⟩
    have hD : Dm (a, b) = Φ (D (a, b)) := hDm (a, b)
    rw [hqeq, hD, hb, hDtop a hp1]


/-- **The cover from the two tubes and the isolation.**  This is the wiring the lead's design uses:
if every preimage of `V` lies in the first sheet's tube `U₁` or on the finger (`hVthin`, which is what
`Work.Drive.PushDisc.exists_isolation_of_whitneyDisc` + a thin `V` supply), and the tube maps into the
plane (`hU₁row`, which the first-sheet flattening supplies), then `hVcover` holds.  Note that the model
disc `Dm` plays no role here: the cover is purely combinatorial in the two tubes. -/
theorem mem_cover_of_tubes {k : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M) (X' : ℝ)
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (V : Set (Work.Drive.Whitney.Mdl k))
    (U₁ : Set M)
    (hU₁row : ∀ x : M, x ∈ U₁ →
      Φ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0})
    (hVthin : ∀ z : M, Φ (f z) ∈ V → z ∈ U₁ ∨ z ∈ σ₂ '' asymReg k X') :
    ∀ z : M, Φ (f z) ∈ V →
      Φ (f z) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
      ∨ (∃ q : ℝ × EuclideanSpace ℝ (Fin k),
          q ∈ asymReg k X' ∧ Φ (f (σ₂ q)) = Φ (f z))
      ∨ Φ (f z) ∈ Dm '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  rcases hVthin z hz with h | h
  · exact Or.inl (hU₁row z h)
  · obtain ⟨q, hq, hqz⟩ := h
    exact Or.inr (Or.inl ⟨q, hq, by rw [hqz]⟩)

/-- **The whole chart from the chart rows, the isolation row and the flat tube.**  This is the
`hiso` half in the form the lead's design asks for: the chart rows, the first sheet's tube `U₁`
mapping into the plane (`hU₁row`), the isolation `hVthin` (the preimages of `V` lie in the two tubes —
supplied by `Work.Drive.PushDisc.exists_isolation_of_whitneyDisc` with `V` thin), the model disc
`Dm = Φ ∘ D` of the smooth Whitney disc (for the cleanliness) and the smallness `hVW`. -/
theorem nonempty_windowChartData_of_isolation {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (k : ℕ) (hk : n = k + 1) (X' : ℝ) (hX' : 1 < X')
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ)
    (h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X'))
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M)
    (hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2))
    (hp₂ : σ₂ ((-1 : ℝ), 0) = p₂) (hq₂ : σ₂ ((1 : ℝ), 0) = q₂)
    (hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X''))
    (hW₀W : σ₂ '' asymReg k X' ⊆ W)
    (c : ℝ → ℝ) (hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0))
    (hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X',
      ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖)
    (hcm : c (-1) = 0) (hc1 : c 1 = 0)
    (hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x)
    (hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0)
    (hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
      ∀ x ∈ frontier (σ₂ '' asymReg k X''),
        |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1)
    (hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0))
    (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (hDm : ∀ p : ℝ × ℝ, Dm p = Φ (D p))
    (hDclean : ∀ z : M, f z ∉ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1))
    (U₁ : Set M)
    (hU₁row : ∀ x : M, x ∈ U₁ →
      Φ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0})
    (V : Set (Work.Drive.Whitney.Mdl k)) (hVo : IsOpen V) (hVD : asymDisc k c ⊆ V)
    (hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W)
    (hVthin : ∀ z : M, Φ (f z) ∈ V → z ∈ U₁ ∨ z ∈ σ₂ '' asymReg k X') :
    Nonempty (WhitneyChartWindowData n f W p₁ p₂ q₁ q₂) := by
  subst hk
  refine nonempty_windowChartData_of_rows f W p₁ p₂ q₁ q₂ hfp hfq hclean k rfl X' hX' Φ Θ hΦsm
    hΘsm hΘΦ hΦΘ h hh σ₂ hσ₂ hp₂ hq₂ hW₀o hW₀W c hcsm hcore hlip hcm hc1 hcpos hcneg hfrontier
    hp₁c hq₁c Dm V hVo hVD hVW ?_ ?_
  · exact mem_cover_of_tubes f Φ σ₂ X' Dm V U₁ hU₁row hVthin
  · exact not_mem_modelDisc_image f Φ Θ hΘΦ D Dm hDm hDclean

end Work.Drive.PushDisc
