
import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.towerDefs
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLComp.LeafDefs

noncomputable section
namespace Work.EKLC6Route
open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLC6Core

-- (repair note: `open Classical` is needed for the `Decidable` instance in `Window.dU`;
--  the statements are otherwise verbatim as in C6GEOM_ROUTE_LEAD.md §3.0)
open Classical

abbrev Tm (t : Fin 3 → ℝ) : X3 → X3 := fun x => aDiag t • x

/-- `G⁰G⁺(t)`: vanishing at the contracted positions. -/
def VtSet (t : Fin 3 → ℝ) : Set SL3 :=
  {g | ∀ i j : Fin 3, t i < t j → (g : Matrix (Fin 3) (Fin 3) ℝ) i j = 0}

def dev (g : SL3) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Fin 3 × Fin 3 =>
    |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)

def betaExp (t : Fin 3 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|)

def lamExp (t : Fin 3 → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun p : Fin 3 × Fin 3 => if t p.1 < t p.2 then t p.2 - t p.1 else 1)

def gridIdx (ρ : ℝ) (L : ℕ) (k : SL3) : Fin 3 → Fin 3 → ℤ :=
  fun i j => ⌊((k : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
    * 2 ^ L / ρ⌋

def gridLev (t : Fin 3 → ℝ) (i : ℕ) : ℕ := ⌈betaExp t * i / Real.log 2⌉₊

def chartSet (t : Fin 3 → ℝ) (z0 : X3) (uc θ : X3 → SL3) (a b : ℝ) : Set X3 :=
  {x | uc x ∈ Work.EKLComp.Uball (Uminus t) a ∧ θ x ∈ VtSet t ∩ V b ∧ (uc x * θ x) • z0 = x}

structure Chart (μ : Measure X3) (t : Fin 3 → ℝ) where
  z0 : X3
  r : ℝ
  ρ : ℝ
  δ : ℝ
  uc : X3 → SL3
  θ : X3 → SL3
  hr : 0 < r
  hρ : 0 < ρ
  hδ : 0 < δ
  hδ1 : δ ≤ 1 / 100
  hrδ : 4000 * r ≤ δ
  hρδ : 4000 * ρ ≤ δ
  huc : Measurable uc
  hθ : Measurable θ
  coord : ∀ u ∈ Work.EKLComp.Uball (Uminus t) (2 * r), ∀ k ∈ VtSet t ∩ V (2 * ρ),
    uc ((u * k) • z0) = u ∧ θ ((u * k) • z0) = k
  inj : ∀ u ∈ Work.EKLComp.Uball (Uminus t) (2 * r), ∀ k ∈ VtSet t ∩ V (2 * ρ),
    ∀ g h : SL3, g ∈ V δ → h ∈ V δ → g • ((u * k) • z0) = h • ((u * k) • z0) → g = h
  pos : 0 < μ (chartSet t z0 uc θ r ρ)
  thin : ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
    μ {x | x ∈ chartSet t z0 uc θ (2 * r) ρ ∧ |dev (uc x) - r| ≤ ε} ≤ ENNReal.ofReal (c * ε)

structure Window (μ : Measure X3) (t : Fin 3 → ℝ) extends Chart μ t where
  C : ℕ → Set SL3
  lev : ℕ → ℕ
  hC0 : C 0 = VtSet t ∩ V ρ
  hCmeas : ∀ j, MeasurableSet (C j)
  hCanti : Antitone C
  hCsmall : ∀ j, ∀ k ∈ C j, ∀ k' ∈ C j, k' * k⁻¹ ∈ V ((1 / 2 : ℝ) ^ j * δ / 100)
  hCpos : ∀ j, 0 < μ (chartSet t z0 uc θ r ρ ∩ θ ⁻¹' C j)
  hCtail : ∀ j, μ ((chartSet t z0 uc θ r ρ ∩ θ ⁻¹' C j) \
      ⋂ i, (chartSet t z0 uc θ r ρ ∩ θ ⁻¹' C i)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j)

namespace Window
variable {μ : Measure X3} {t : Fin 3 → ℝ} (w : Window μ t)

def W : Set X3 := chartSet t w.z0 w.uc w.θ w.r w.ρ

def dU (z : X3) : ℝ :=
  if z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ then |dev (w.uc z) - w.r| else w.r

def N0 : Set X3 := neverReturnSet t w.W ∪ {z | w.dU z = 0}

def Jset : Option ℕ → Set X3
  | some j => w.W ∩ w.θ ⁻¹' (w.C j \ w.C (j + 1))
  | none => w.W ∩ w.θ ⁻¹' (⋂ i, w.C i)

def D (i : ℕ) (J : Option ℕ) (c : Fin 3 → Fin 3 → ℤ) : Set X3 :=
  if i = 0 then ∅ else
    (firstReturnSet t w.W i ∩ w.Jset J ∩ {x | gridIdx w.ρ (gridLev t i) (w.θ x) = c}) \ w.N0

abbrev PIdx := Option (Option (ℕ × Option ℕ × (Fin 3 → Fin 3 → ℤ)))

def piece : PIdx → Set X3
  | none => (w.W ∪ w.N0)ᶜ
  | some none => w.N0
  | some (some p) => w.D p.1 p.2.1 p.2.2

def S (n : ℕ) : Set X3 :=
  haveI : Encodable PIdx := Encodable.ofCountable _
  match Encodable.decode₂ PIdx n with
  | some p => w.piece p
  | none => ∅

def A : MeasurableSpace X3 := pastSigSet t w.S

end Window
end Work.EKLC6Route
