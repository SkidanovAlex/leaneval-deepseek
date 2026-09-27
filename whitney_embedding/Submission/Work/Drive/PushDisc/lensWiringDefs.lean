import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.thetaMapDefs
import Submission.Work.Drive.PushDisc.lensNhd

/-!
# The bundled data structures of the lens wiring

These are the *interfaces* through which the sub-lemmas of `lensWiringSolid` are stated:
`LWFingerChart` (the finger's `(x,v)`-chart with its window), `LWFlatTube` (the flat first tube
of S5), `LWLensDisc` (the clean lens approximation `Δ` with its finger frame `V`).
-/

open scoped ContDiff Manifold
open Set Metric

namespace Work.Drive.PushDisc

/-- **The finger's `(x,v)`-chart with a window inside its target** (the strengthened
`exists_chart_of_arc`): the chart straightens the second arc, its source avoids `p₁` and `q₁`, and a
rescaled window of parameters lies in its target. -/
structure LWFingerChart (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) where
  c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))
  hcsmooth : Work.Whitney.IsSmoothChart c
  hcsrc : c.source ⊆ C.W
  hcarc : C.γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ c.source
  hp₁c : C.p₁ ∉ c.source
  hq₁c : C.q₁ ∉ c.source
  harc₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c (C.γ₂ t) = splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k)))
  X' : ℝ
  hX' : 1 < X'
  r : ℝ
  hr : 0 < r
  /-- the window of the finger's chart: `|x| ≤ X'`, `‖v‖ ≤ 1`, scaled by `r` -/
  hwin : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ X' → ‖p.2‖ ≤ 1 →
      splitE k (p.1, r • p.2) ∈ c.target

/-- **The flat first tube of S5** (`straightFlatTubeArc`), in the vocabulary of a chart
`Φ₀ : ℝ^{2n} → Mdl k` that flattens the first sheet and straightens the first arc. -/
structure LWFlatTube (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) where
  Φ₀ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k
  Θ₀ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1)))
  hΦ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ₀
  hΘ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ₀
  hΘ₀Φ₀ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ₀ (Φ₀ y) = y
  hΦ₀Θ₀ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ₀ (Θ₀ ξ) = ξ
  U₁ : Set M
  hU₁o : IsOpen U₁
  hU₁W : U₁ ⊆ C.W
  hU₁arc : C.γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁
  hp₂U₁ : C.p₂ ∉ U₁
  hq₂U₁ : C.q₂ ∉ U₁
  hU₁row : ∀ x : M, x ∈ U₁ → Φ₀ (C.f x) ∈ Work.Drive.Whitney.sheetA
  δ₀ : ℝ
  hδ₀ : 0 < δ₀
  hseg : ∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ₀ (C.f z) = (x, 0, 0, 0)
  hpin₁ : Φ₀ (C.f C.p₁) = ((-1 : ℝ), 0, 0, 0)
  hpin₂ : Φ₀ (C.f C.p₂) = ((-1 : ℝ), 0, 0, 0)
  hpin₃ : Φ₀ (C.f C.q₁) = ((1 : ℝ), 0, 0, 0)
  hpin₄ : Φ₀ (C.f C.q₂) = ((1 : ℝ), 0, 0, 0)
  harc₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Φ₀ (C.f (C.γ₁ t)) = (((2 : ℝ) * t - 1), 0, 0, 0)

/-- **The finger's parametrisation `S₂` with its frame `V`** (the globally smooth parametrisation
of the finger in the `Φ₀`-chart, with the rows on the window of `F`). -/
structure LWFingerData (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (T : LWFlatTube k M C) (F : LWFingerChart k M C) where
  S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k
  hS₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂
  /-- `S₂` is the finger's chart parametrisation on the window of `F` -/
  hS₂ag : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ F.X' → ‖p.2‖ ≤ F.r →
      S₂ p = T.Φ₀ (C.f (F.c.symm (splitE k p)))
  hS₂d : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ F.X' → ‖p.2‖ ≤ F.r →
      fderiv ℝ S₂ p = fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
        T.Φ₀ (C.f (F.c.symm (splitE k q)))) p
  hS₂inj : Set.InjOn S₂ {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ F.X' ∧ ‖p.2‖ ≤ F.r}
  hS₂imm : ∀ p ∈ {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ F.X' ∧ ‖p.2‖ ≤ F.r},
      Function.Injective (fderiv ℝ S₂ p)
  V : ℝ → Fin k → Work.Drive.Whitney.Mdl k
  hVsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V
  hVdef : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| ≤ F.X' →
      (fderiv ℝ (fun w' : EuclideanSpace ℝ (Fin k) => S₂ (x, w')) 0) w = ∑ j : Fin k, w j • V x j

/-- **The clean lens approximation `Δ`** (A2, `exists_cleanLens`), with the rows the assembly
consumes. -/
structure LWLensDisc (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (T : LWFlatTube k M C) (F : LWFingerChart k M C)
    (G : LWFingerData k M C T F) where
  Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k
  hΔsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ
  hΔ0 : ∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0)
  hΔ1 : ∀ x : ℝ, |x| ≤ F.X' → Δ (x, arch x) = G.S₂ (x, 0)
  hΔinj : Set.InjOn Δ lensK
  hΔimm : ∀ p ∈ lensK, Function.Injective (fderiv ℝ Δ p)
  hΔclean : ∀ p ∈ lensKo, ∀ z : M, Δ p ≠ T.Φ₀ (C.f z)
  hbot : ∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ
      (Fin.append (planeFrame k (fun q => fderiv ℝ Δ q (1, 0)) (fun q => fderiv ℝ Δ q (0, 1))
        (x, 0)) (iotaU k))
  htop : ∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ
      (Fin.append (planeFrame k (fun q => fderiv ℝ Δ q (1, 0)) (fun q => fderiv ℝ Δ q (0, 1))
        (x, arch x)) (G.V x))

/-- **A chart of the first arc inside the flat tube** (for the corner-sign producer `B2`). -/
structure LWFirstArcChart (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (T : LWFlatTube k M C) where
  c₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))
  hc₁ : Work.Whitney.IsSmoothChart c₁
  hsrc₁ : c₁.source ⊆ T.U₁
  hc₁arc : C.γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ c₁.source
  hp₁c₁ : C.p₁ ∈ c₁.source
  hq₁c₁ : C.q₁ ∈ c₁.source
  hsh₁ : ∀ x : M, x ∈ c₁.source →
      (T.Φ₀ (C.f x)).2.1 = 0 ∧ (T.Φ₀ (C.f x)).2.2.2 = 0

/-- **The two frames `U`, `W` of the lens chart** (C2, `lensFramesWide`). -/
structure LWFrames (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (T : LWFlatTube k M C) (F : LWFingerChart k M C)
    (G : LWFingerData k M C T F) (D : LWLensDisc k M C T F G) where
  X' : ℝ
  hX' : 1 < X'
  U : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k
  W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k
  hUsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U
  hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W
  hU0 : ∀ x : ℝ, U (x, 0) = iotaU k
  hWtop : ∀ x : ℝ, |x| ≤ X' → W (x, arch x) = G.V x
  hframe : ∀ p ∈ lensK, LinearIndependent ℝ
      (Fin.append (Fin.append (planeFrame k (fun q => fderiv ℝ D.Δ q (1, 0))
        (fun q => fderiv ℝ D.Δ q (0, 1)) p) (U p)) (W p))

/-- **The global framing diffeomorphism of the `θ`-assembly**, with the thin `u`-row and the three
rows the assembly consumes (D1/D3, `lensThetaGlobal`). -/
structure LWTheta (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : LWConfig (k + 1) M) (T : LWFlatTube k M C) (F : LWFingerChart k M C)
    (G : LWFingerData k M C T F) (D : LWLensDisc k M C T F G) (Fr : LWFrames k M C T F G D) where
  r : ℝ
  X'' : ℝ
  ε : ℝ
  hr : 0 < r
  hrρ : r ≤ F.r
  hX'' : 1 < X''
  hX''X' : X'' ≤ F.X'
  hε : 0 < ε
  Θg : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k
  Θgi : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k
  hΘgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θg
  hΘgism : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θgi
  hlΘ : Function.LeftInverse Θgi Θg
  hrΘ : Function.RightInverse Θgi Θg
  hplane0 : ∀ (x : ℝ) (u : EuclideanSpace ℝ (Fin k)), |x| ≤ X'' → ‖u‖ ≤ ε →
      Θg (x, 0, u, 0) = (x, 0, u, 0)
  hdisc : ∀ x y : ℝ, |x| ≤ X'' → 0 ≤ y → y ≤ arch x → Θg (x, y, 0, 0) = D.Δ (x, y)
  hfinger : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X'' → ‖w‖ < 1 →
      Θg (x, arch x, 0, w) = G.S₂ (x, r • w)

end Work.Drive.PushDisc
