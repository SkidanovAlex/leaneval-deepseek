import Mathlib
import Submission.Work.Cert.WindDefs
import Submission.CDTPlan.InterfacesA

/-! # Theorem-A arc certificate: specification (orchestrator-owned contracts, definitions only).

The lead builds the integer checker (`Defs.lean`: `leafOK`; `WindDefs.lean`: `windLeafOK`) and the
certificate chunks (`Chunks/C###.lean`, `WChunks/W###.lean`, linked in `Final.lean`, `WindFinal.lean`).
The agents prove the soundness `Prop`s below and assemble ANumerics conjunct 2 and the outer winding. -/
namespace Work.Cert
open Complex Submission.CDTPlan

/-- a scaled complex number `(x + y i)/S`. -/
noncomputable def cx (x y : ℤ) : ℂ := (((x : ℝ) / (S : ℝ) : ℝ) : ℂ) + (((y : ℝ) / (S : ℝ) : ℝ) : ℂ) * I

/-- centre and radius (mantissas at scale `S`) of the input disc of a leaf — EXACTLY the values used
inside `leafOK` / `qChain`. -/
def leafCx (L : Leaf) : Int := fdiv (L.Ax + L.Bx) 2
def leafCy (L : Leaf) : Int := fdiv (L.Ay + L.By) 2
def leafRz (L : Leaf) : Int := fdiv L.chU 2 + 1 + dvu (mu L.chU L.chU) (2 * Rk L.k) + 1 + ETOL
noncomputable def leafC (L : Leaf) : ℂ := cx (leafCx L) (leafCy L)
noncomputable def leafR (L : Leaf) : ℝ := (leafRz L : ℝ) / (S : ℝ)

/-- the geometric part of `leafOK` (the `okA` conjunct): short CCW arc between near-circle points. -/
def geomOK (L : Leaf) : Bool :=
  let R := Rk L.k
  let dx := L.Bx - L.Ax
  let dy := L.By - L.Ay
  decide (0 ≤ L.chU) && decide (dx * dx + dy * dy ≤ L.chU * L.chU) &&
    decide (dx * dx + dy * dy < fdiv (R * R) 4) && decide (0 < L.Ax * L.By - L.Ay * L.Bx) &&
    decide (0 < L.Ax * L.Bx + L.Ay * L.By) &&
    decide (iabs (L.Ax * L.Ax + L.Ay * L.Ay - R * R) ≤ 2 * R * CTOL) &&
    decide (iabs (L.Bx * L.Bx + L.By * L.By - R * R) ≤ 2 * R * CTOL)

/-- Jacobi theta series: `A(q) = Σ_{n≥0} q^{n(n+1)/2}`, `B(q) = 1 + 2 Σ_{n≥1} (-1)^n q^{n²}`. -/
noncomputable def thetaA (q : ℂ) : ℂ := ∑' n : ℕ, q ^ (n * (n + 1) / 2)
noncomputable def thetaB (q : ℂ) : ℂ := 1 + 2 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2)

/-! ## The soundness contracts -/

/-- the rotation constants of the four slit stages and the grid step `W ≈ e^{2πi/4096}`. -/
def RotConsts : Prop :=
  ‖cx rot0r rot0i - rot (2033 / 25000)‖ ≤ 2 / (S : ℝ) ∧
  ‖cx rot1r rot1i - rot (2927 / 25000)‖ ≤ 2 / (S : ℝ) ∧
  ‖cx rot2r rot2i - rot (453 / 12500)‖ ≤ 2 / (S : ℝ) ∧
  ‖cx rot3r rot3i - rot (-1971 / 25000)‖ ≤ 2 / (S : ℝ) ∧
  ‖cx WR WI - rot (1 / 4096)‖ ≤ 2 / (S : ℝ)

/-- `expLo x` is a lower bound of `S·exp(x/S)`. -/
def ExpLoSound : Prop := ∀ x : ℤ, (expLo x : ℝ) ≤ (S : ℝ) * Real.exp ((x : ℝ) / (S : ℝ))

/-- one rotated slit stage maps its input disc into its output disc. -/
def SlitStageSound : Prop :=
  ∀ (r t : ℝ) (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW),
    0 < r → r < 1 →
    (A : ℝ) = S * (1 + r) ^ 2 → (B2 : ℝ) = S * (2 * (1 - 6 * r + r ^ 2)) → (E : ℝ) = S * (2 * (r - 1) ^ 2) →
    (C1 : ℝ) = S * (1 + r) → (G8 : ℝ) = S * (8 * r) → (A2 : ℝ) = S * (2 * (1 + r) ^ 2) →
    ‖cx ror roi - rot t‖ ≤ 2 / (S : ℝ) →
    (slitStage A B2 E C1 G8 A2 ror roi st w).ok = true →
    ∀ z : ℂ, ‖z - cx st.cr st.ci‖ ≤ (st.rho : ℝ) / S →
      ‖rot t * slit r z - cx (slitStage A B2 E C1 G8 A2 ror roi st w).cr
          (slitStage A B2 E C1 G8 A2 ror roi st w).ci‖ ≤
        ((slitStage A B2 E C1 G8 A2 ror roi st w).rho : ℝ) / S

/-- the lune stage (`v = lune(36/5, -u)`) maps its input disc into its output disc. -/
def LuneStageSound : Prop :=
  ∀ (st : St) (w : LuneW), (luneStage st w).ok = true →
    ∀ z : ℂ, ‖z - cx st.cr st.ci‖ ≤ (st.rho : ℝ) / S →
      ‖lune (36 / 5) (-z) - cx (luneStage st w).cr (luneStage st w).ci‖ ≤ ((luneStage st w).rho : ℝ) / S

/-- the truncated theta sums with their derivative/tail radii enclose `A`, `B` on the `q` disc. -/
def ThetaEncl : Prop :=
  ∀ (qr qi rq mU : ℤ), 0 ≤ mU → qr * qr + qi * qi ≤ mU * mU → 0 ≤ rq →
    mU + rq + 1 ≤ fdiv (79 * S) 100 →
    ∀ q : ℂ, ‖q - cx qr qi‖ ≤ (rq : ℝ) / S →
      (let m := mU + rq + 1
       let A := aLoop qr qi rq m KTH 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩
       let tailA := dvu (mu A.mT (mu A.mn m + 1)) (S - m) + 1
       ‖thetaA q - cx A.Ar A.Ai‖ ≤ ((A.dA + tailA : ℤ) : ℝ) / S) ∧
      (let m := mU + rq + 1
       let B := bLoop (cmr qr qi qr qi) (cmi qr qi qr qi) rq m KTH 1 ⟨qr, qi, S, 0, S, 0, m, S, 0⟩
       let tailB := 2 * dvu (mu B.ms B.mo) (S - m) + 1
       ‖thetaB q - cx B.Br B.Bi‖ ≤ ((B.dB + tailB : ℤ) : ℝ) / S)

/-- Jacobi's product-to-theta identity for the Hauptmodul `h`. -/
def ThetaIdentity : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → hauptH q * thetaB q ^ 8 = -256 * q * thetaA q ^ 8

/-- per-leaf log bound (conjunct 2). -/
def LeafSound : Prop :=
  ∀ L : Leaf, leafOK L = true →
    ∀ z : ℂ, ‖z - leafC L‖ ≤ leafR L → ‖phiA z‖ ≤ Real.exp ((L.G : ℝ) / S)

/-- per-leaf half-plane (winding). -/
def WindLeafSound : Prop :=
  ∀ (lab : ℕ) (L : Leaf) (bU : ℤ), windLeafOK lab L bU = true →
    ∀ z : ℂ, ‖z - leafC L‖ ≤ leafR L → 0 < ((phiA z + 1 / 72) * star (I ^ lab)).re

/-- a chain of leaves between two grid points covers the corresponding arc of the circle `|z| = Rk k / S`. -/
def ArcCover : Prop :=
  ∀ (k j : ℕ) (Ex Ey nx ny : ℤ) (ls : List Leaf), k ≤ 2 → j < 4096 →
    ‖cx Ex Ey - ((Rk k : ℝ) / S : ℝ) * rot ((j : ℝ) / 4096)‖ ≤ 65536 / (S : ℝ) →
    ‖cx nx ny - ((Rk k : ℝ) / S : ℝ) * rot (((j : ℝ) + 1) / 4096)‖ ≤ 65536 / (S : ℝ) →
    (match ls with | [] => false | l :: _ => decide (l.Ax = Ex) && decide (l.Ay = Ey)) = true →
    chainOK nx ny ls = true → ls.all (fun l => decide (l.k = k) && geomOK l) = true →
    ∀ t ∈ Set.Icc ((j : ℝ) / 4096) (((j : ℝ) + 1) / 4096),
      ∃ l ∈ ls, ‖((Rk k : ℝ) / S : ℝ) * rot t - leafC l‖ ≤ leafR l


/-! ## Certificate facts (abstract interface; proved once from the chunk modules, consumed without them) -/

/-- integer block weights (denominator `DENS = 500·14·4096`) of `γ = (0, 71/125, 277/100, 14)`. -/
def wtS (k : ℕ) : ℤ := if k = 0 then 284 else if k = 1 then 1101 else 5615
def DENS : ℤ := 28672000

/-- What the conjunct-2 certificate (Chunks + Final) establishes, stated without any certificate data:
per circle `k ≤ 2` and arc `j < 4096` a grid point `E k j` (with `E k 0 = E k 4096 = (Rk k, 0)`), a leaf
list chained from `E k j` to `E k (j+1)`, all leaves `leafOK` with `G ≤ G k j`, and the weighted
max-sum `≤ 11.2` (units `S·DENS²`). -/
def Conj2Cert : Prop :=
  ∃ (G : ℕ → ℕ → ℤ) (E : ℕ → ℕ → ℤ × ℤ) (LS : ℕ → ℕ → List Leaf),
    (∀ k, k ≤ 2 → E k 0 = (Rk k, 0) ∧ E k 4096 = (Rk k, 0)) ∧
    (∀ k j, k ≤ 2 → j < 4096 →
      (match LS k j with | [] => false | l :: _ => decide (l.Ax = (E k j).1) && decide (l.Ay = (E k j).2)) = true ∧
      chainOK (E k (j + 1)).1 (E k (j + 1)).2 (LS k j) = true ∧
      gridStep (E k j).1 (E k j).2 (E k (j + 1)).1 (E k (j + 1)).2 = true ∧
      (LS k j).all (fun l => decide (l.k = k) && decide (l.G ≤ G k j) && leafOK l) = true) ∧
    (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 4096, ∑ j' ∈ Finset.range 4096,
        wtS k * wtS k' * max (G k j) (G k' j')) ≤ 112 * DENS * DENS * S / 10

/-- What the winding certificate (WChunks + WindFinal) establishes: per arc `j < 4096` of `|z| = 1` a label,
a grid point (`E 0 = E 4096 = (S, 0)`), a leaf list chained from `E j` to `E (j+1)` with all leaves
`windLeafOK (lab j)`, and the cyclic label sequence has quarter-turn sum 4. -/
def WindCertFacts : Prop :=
  ∃ (lab : ℕ → ℕ) (E : ℕ → ℤ × ℤ) (LS : ℕ → List (Leaf × ℤ)),
    E 0 = (S, 0) ∧ E 4096 = (S, 0) ∧
    (∀ j, j < 4096 →
      (match LS j with | [] => false | l :: _ => decide (l.1.Ax = (E j).1) && decide (l.1.Ay = (E j).2)) = true ∧
      wchainOK (E (j + 1)).1 (E (j + 1)).2 (LS j) = true ∧
      gridStep (E j).1 (E j).2 (E (j + 1)).1 (E (j + 1)).2 = true ∧
      (LS j).all (fun l => windLeafOK (lab j) l.1 l.2) = true) ∧
    labelsOK ((List.range 4096).map lab) = true


/-! ## v4 (2026-09-29): conjunct 2 on the 1024-grid (`NARC2`). The 4096-grid Props above stay for the winding. -/

/-- the conjunct-2 grid step constant `W2 ≈ e^{2πi/1024}`. -/
def RotConsts2 : Prop := ‖cx WR2 WI2 - rot (1 / (NARC2 : ℝ))‖ ≤ 2 / (S : ℝ)

/-- `ArcCover` on the `NARC2`-grid. -/
def ArcCover2 : Prop :=
  ∀ (k j : ℕ) (Ex Ey nx ny : ℤ) (ls : List Leaf), k ≤ 2 → j < NARC2 →
    ‖cx Ex Ey - ((Rk k : ℝ) / S : ℝ) * rot ((j : ℝ) / NARC2)‖ ≤ 65536 / (S : ℝ) →
    ‖cx nx ny - ((Rk k : ℝ) / S : ℝ) * rot (((j : ℝ) + 1) / NARC2)‖ ≤ 65536 / (S : ℝ) →
    (match ls with | [] => false | l :: _ => decide (l.Ax = Ex) && decide (l.Ay = Ey)) = true →
    chainOK nx ny ls = true → ls.all (fun l => decide (l.k = k) && geomOK l) = true →
    ∀ t ∈ Set.Icc ((j : ℝ) / NARC2) (((j : ℝ) + 1) / NARC2),
      ∃ l ∈ ls, ‖((Rk k : ℝ) / S : ℝ) * rot t - leafC l‖ ≤ leafR l

/-- weight denominator on the 1024-grid: `500·14·1024`. -/
def DENS2 : ℤ := 7168000

/-- `Conj2Cert` on the `NARC2`-grid (grid step `gridStep2`, weights `wtS k / DENS2`). -/
def Conj2Cert2 : Prop :=
  ∃ (G : ℕ → ℕ → ℤ) (E : ℕ → ℕ → ℤ × ℤ) (LS : ℕ → ℕ → List Leaf),
    (∀ k, k ≤ 2 → E k 0 = (Rk k, 0) ∧ E k NARC2 = (Rk k, 0)) ∧
    (∀ k j, k ≤ 2 → j < NARC2 →
      (match LS k j with | [] => false | l :: _ => decide (l.Ax = (E k j).1) && decide (l.Ay = (E k j).2)) = true ∧
      chainOK (E k (j + 1)).1 (E k (j + 1)).2 (LS k j) = true ∧
      gridStep2 (E k j).1 (E k j).2 (E k (j + 1)).1 (E k (j + 1)).2 = true ∧
      (LS k j).all (fun l => decide (l.k = k) && decide (l.G ≤ G k j) && leafOK l) = true) ∧
    (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range NARC2, ∑ j' ∈ Finset.range NARC2,
        wtS k * wtS k' * max (G k j) (G k' j')) ≤ 112 * DENS2 * DENS2 * S / 10

end Work.Cert
