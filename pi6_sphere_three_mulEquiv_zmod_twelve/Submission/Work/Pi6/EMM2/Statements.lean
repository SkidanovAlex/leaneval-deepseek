import Submission.Work.Pi6.EMM2.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The interfaces of the EMM2 areas

The three forcing arguments (`k2f`, `k3f`, `k4f`) and the final assembly `Work.Pi6.emMod2` are
written against the *statements* collected here, each of which is proved elsewhere in
`Submission/Work/Pi6/EMM2/`.
-/

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits

/-- The `K(ℤ,2)`-from-`S²` model and the reduction map `r` (`Pi6/EMM2/kZmodel`). -/
abbrev KZModelStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
    ∃ (KZ : Type) (tKZ : TopologicalSpace KZ) (k₀ : KZ)
      (r : @ContinuousMap KZ X tKZ (inferInstance : TopologicalSpace X)),
      letI : TopologicalSpace KZ := tKZ
      r k₀ = x₀ ∧
      Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N KZ k₀ ∧
      Function.Surjective (Work.StemsB.πmap r 1 k₀) ∧
      Function.Surjective (Work.Pi6.hmap ℤ r 2).hom ∧
      Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1)
        (Work.StemsB.fibre (Work.Serre.mpathQ r) (r k₀))
        (Work.StemsB.fibrePoint (Work.Serre.mpathQ r) (Work.Serre.mpathOf r k₀))

/-- Finiteness of the cohomology of a range model (`Pi6/EMM2/finiteType`). -/
abbrev FiniteTypeStatement : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] {A : Type} [AddCommGroup A] (_hA : Module.Finite ℤ A)
    {m N : ℕ} (_hm : 2 ≤ m) {X : Type} [TopologicalSpace X] (x : X)
    (_hX : Work.Serre.IsEMSpaceUpTo A m (by omega) (N + 1) X x),
    ∀ n : ℕ, n ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 X n)

/-- Low-degree cohomology of a range model (`Pi6/EMM2/lowDegree`). -/
abbrev LowDegreeStatement : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] {A : Type} [AddCommGroup A] (_hA : Module.Finite ℤ A)
    {m M : ℕ} (_hm : 2 ≤ m) (_hM : m ≤ M) {X : Type} [TopologicalSpace X] (x : X)
    (_hX : Work.Serre.IsEMSpaceUpTo A m (by omega) M X x),
    Work.PiS.SimplyConn X x ∧
      Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = 1 ∧
      (∀ i : ℕ, 1 ≤ i → i < m → IsZero (Work.Pi6.Coh 𝕜 X i))

/-- The field facts for a `K(ℤ,2)` range model through degree `9` (`Pi6/EMM2/k2field`). -/
abbrev K2FieldStatement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (𝕜 : Type) [Field 𝕜] {X : Type} [TopologicalSpace X] (x : X)
    {M : ℕ}, 9 ≤ M → Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) M X x →
    ∃ w : Work.Pi6.Coh 𝕜 X 2,
      w ≠ 0 ∧
      (∀ k : ℕ, k ≤ 4 → Work.Pi6.cpow w k ≠ 0) ∧
      (∀ k : ℕ, k ≤ 4 → Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X (2 * k)) = 1) ∧
      (∀ k : ℕ, k ≤ 4 → Subsingleton (Work.Pi6.Coh 𝕜 X (2 * k + 1)))

/-- `H²` of a `K(ℤ/2,2)` range model over a field of characteristic `2`
(`Pi6/EMM2/secondCohZModTwo`). -/
abbrev SecondCohZModTwoStatement : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] (_h2 : CharP 𝕜 2) {X : Type} [TopologicalSpace X] (x : X)
    {M : ℕ}, 2 ≤ M → Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) M X x →
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 2) = 1

/-- Graded commutativity of the product of a Serre spectral sequence in characteristic `2`
(`Pi6/EMM2/mulComm`). -/
abbrev MulCommStatement : Prop :=
  ∀ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : ContinuousMap E B)
    (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2)) (_hS : Work.Pi6.IsSerreMSS S p e₀ N),
    ∀ (r : ℕ) (a b c : ℤ × ℤ) (_h : a + b = c) (x : S.E r a) (y : S.E r b), 2 ≤ r →
      0 ≤ a.1 → 0 ≤ a.2 → 0 ≤ b.1 → 0 ≤ b.2 → a.1 + b.1 ≤ (N : ℤ) → a.2 + b.2 ≤ (N : ℤ) →
      S.mul r a b c _h x y = S.mul r b a c (by rw [← _h]; abel) y x

/-- The cup-product unit (`Pi6/EMM2/cupOne`). -/
abbrev CupOneStatement : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] {X : Type} [TopologicalSpace X] (n : ℕ) (b : Work.Pi6.Coh 𝕜 X n),
    (Nat.zero_add n) ▸ (Work.Pi6.cup 𝕜 X 0 n (Work.Pi6.one 𝕜 X) b) = b ∧
      Work.Pi6.cup 𝕜 X n 0 b (Work.Pi6.one 𝕜 X) = b

/-- The path fibration of a range model (`Pi6/EMM2/pathFib`). -/
abbrev PathFibStatement : Prop :=
  ∀ {A : Type} [AddCommGroup A] {m M : ℕ} (_hm : 2 ≤ m) {X : Type} [TopologicalSpace X]
    (x₀ : X) (_hX : Work.Serre.IsEMSpaceUpTo A m (by omega) M X x₀),
    ContractibleSpace (Work.Serre.mpath (ContinuousMap.const PUnit x₀)) ∧
      Work.StemsB.IsSerreFibration (Work.Serre.mpathQ (ContinuousMap.const PUnit x₀)) ∧
      Work.Serre.IsEMSpaceUpTo A (m - 1) (by omega) (M - 1)
        (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit x₀)) x₀)
        (Work.StemsB.fibrePoint (Work.Serre.mpathQ (ContinuousMap.const PUnit x₀))
          (Work.Serre.mpathOf (ContinuousMap.const PUnit x₀) PUnit.unit))

/-- **Area EMM2, part 1: the forcing computation for `K(ℤ/2,2)` range models.** -/
abbrev K2FactsStatement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (_hZ : Work.Pi6.K2ZFacts) (_hKZ : KZModelStatement)
    (_hFT : FiniteTypeStatement) (_hLD : LowDegreeStatement) (_h2f : K2FieldStatement)
    (_h2c : SecondCohZModTwoStatement) (_hmc : MulCommStatement) (_hco : CupOneStatement)
    {X : Type} [TopologicalSpace X] (x₀ : X) {N : ℕ}, 10 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 3) ≤ 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 4) ≤ 1 ∧
      (∀ a : Work.Pi6.Coh (ZMod 2) X 2, a ≠ 0 →
        Work.Pi6.cup (ZMod 2) X 2 2 a a ≠ 0) ∧
      (∀ y : Work.Pi6.Coh (ZMod 2) X 3, y ≠ 0 →
        Work.Pi6.cup (ZMod 2) X 3 3 y y ≠ 0)

/-- **Area EMM2, part 2: the forcing computation for `K(ℤ/2,3)` range models.** -/
abbrev K3FactsStatement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (_hZ : Work.Pi6.K2ZFacts) (_hKZ : KZModelStatement)
    (_hFT : FiniteTypeStatement) (_hLD : LowDegreeStatement) (_h2f : K2FieldStatement)
    (_h2c : SecondCohZModTwoStatement) (_hmc : MulCommStatement) (_hco : CupOneStatement)
    (_hPF : PathFibStatement) (_hk2 : K2FactsStatement)
    {X : Type} [TopologicalSpace X] (x₀ : X) {N : ℕ}, 10 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) N X x₀ →
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 3) = 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 4) = 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 5) ≤ 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 6) ≤ 2 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 7) ≤ 2 ∧
      (∀ a : Work.Pi6.Coh (ZMod 2) X 3, a ≠ 0 →
        Work.Pi6.cup (ZMod 2) X 3 3 a a ≠ 0)

/-- **Area EMM2, part 3: the forcing computation for `K(ℤ/2,4)` range models.** -/
abbrev K4FactsStatement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (_hZ : Work.Pi6.K2ZFacts) (_hKZ : KZModelStatement)
    (_hFT : FiniteTypeStatement) (_hLD : LowDegreeStatement) (_h2f : K2FieldStatement)
    (_h2c : SecondCohZModTwoStatement) (_hmc : MulCommStatement) (_hco : CupOneStatement)
    (_hPF : PathFibStatement) (_hk2 : K2FactsStatement) (_hk3 : K3FactsStatement)
    {X : Type} [TopologicalSpace X] (x₀ : X) {N : ℕ}, 10 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) N X x₀ →
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 7) ≤ 2 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 8) ≤ 2


/-! ## Low-threshold variants used to iterate the forcing arguments

The three forcing arguments are chained (`K₂ → K₃ → K₄`), and the fibre of the path fibration of a
range model through `N` is only a range model through `N - 1`.  To iterate with the threshold `10`
of the final statement, the `K(ℤ,2)` input and the `K₂` forcing have to be available at the lower
thresholds `9` (for the `K₃` step) which in turn needs the `K(ℤ,2)` field facts at threshold `8`.
These variants record exactly the thresholds needed. -/

/-- The `K(ℤ,2)`-from-`S²` model through degree `8` (`Pi6/EMM2/kZmodelLow`). -/
abbrev KZModelLowStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ), 8 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
    ∃ (KZ : Type) (tKZ : TopologicalSpace KZ) (k₀ : KZ)
      (r : @ContinuousMap KZ X tKZ (inferInstance : TopologicalSpace X)),
      letI : TopologicalSpace KZ := tKZ
      r k₀ = x₀ ∧
      Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N KZ k₀ ∧
      Function.Surjective (Work.StemsB.πmap r 1 k₀) ∧
      Function.Surjective (Work.Pi6.hmap ℤ r 2).hom ∧
      Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1)
        (Work.StemsB.fibre (Work.Serre.mpathQ r) (r k₀))
        (Work.StemsB.fibrePoint (Work.Serre.mpathQ r) (Work.Serre.mpathOf r k₀))

/-- The field facts for a `K(ℤ,2)` range model through degree `5` (`Pi6/EMM2/k2fieldLow`). -/
abbrev K2FieldLowStatement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (𝕜 : Type) [Field 𝕜] {X : Type} [TopologicalSpace X] (x : X)
    {M : ℕ}, 6 ≤ M → Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) M X x →
    ∃ w : Work.Pi6.Coh 𝕜 X 2,
      w ≠ 0 ∧
      (∀ k : ℕ, k ≤ 2 → Work.Pi6.cpow w k ≠ 0) ∧
      (∀ k : ℕ, k ≤ 2 → Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X (2 * k)) = 1) ∧
      (∀ k : ℕ, k ≤ 2 → Subsingleton (Work.Pi6.Coh 𝕜 X (2 * k + 1)))

/-- **The `K(ℤ/2,2)` forcing at threshold `9`** (`Pi6/EMM2/k2forcing9`): the internal form used by
the `K(ℤ/2,3)` step. -/
abbrev K2Facts9Statement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (_hKZ : KZModelLowStatement) (_hFT : FiniteTypeStatement)
    (_hLD : LowDegreeStatement) (_h2f : K2FieldLowStatement)
    (_h2c : SecondCohZModTwoStatement) (_hmc : MulCommStatement) (_hco : CupOneStatement)
    {X : Type} [TopologicalSpace X] (x₀ : X) {N : ℕ}, 8 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 3) ≤ 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 4) ≤ 1 ∧
      (∀ a : Work.Pi6.Coh (ZMod 2) X 2, a ≠ 0 →
        Work.Pi6.cup (ZMod 2) X 2 2 a a ≠ 0) ∧
      (∀ y : Work.Pi6.Coh (ZMod 2) X 3, y ≠ 0 →
        Work.Pi6.cup (ZMod 2) X 3 3 y y ≠ 0)

/-- **The `K(ℤ/2,3)` forcing at threshold `9`** (`Pi6/EMM2/k3forcing9`). -/
abbrev K3Facts9Statement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (_hKZ : KZModelLowStatement) (_hFT : FiniteTypeStatement)
    (_hLD : LowDegreeStatement)
    (_h2f : K2FieldLowStatement) (_h2c : SecondCohZModTwoStatement) (_hmc : MulCommStatement)
    (_hco : CupOneStatement) (_hPF : PathFibStatement) (_hk2 : K2Facts9Statement)
    {X : Type} [TopologicalSpace X] (x₀ : X) {N : ℕ}, 9 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) N X x₀ →
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 3) = 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 4) = 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 5) ≤ 1 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 6) ≤ 2 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 7) ≤ 2 ∧
      (∀ a : Work.Pi6.Coh (ZMod 2) X 3, a ≠ 0 →
        Work.Pi6.cup (ZMod 2) X 3 3 a a ≠ 0)

/-- **The `K(ℤ/2,4)` forcing at threshold `10`** (`Pi6/EMM2/k4forcing9`), with the threshold-`9`
`K₃` facts as its input. -/
abbrev K4FactsLowStatement : Prop :=
  ∀ (_hM : Work.Pi6.MSSHolds) (_hKZ : KZModelLowStatement) (_hFT : FiniteTypeStatement)
    (_hLD : LowDegreeStatement) (_h2f : K2FieldLowStatement) (_h2c : SecondCohZModTwoStatement)
    (_hmc : MulCommStatement) (_hco : CupOneStatement) (_hPF : PathFibStatement)
    (_hk2 : K2Facts9Statement) (_hk3 : K3Facts9Statement)
    {X : Type} [TopologicalSpace X] (x₀ : X) {N : ℕ}, 10 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) N X x₀ →
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 7) ≤ 2 ∧
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) X 8) ≤ 2

end Work.Pi6.EMM2
