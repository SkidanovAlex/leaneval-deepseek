import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.IndRepModel
import Submission.Work.Induction.exists_fdRep_of_representation
import Submission.Work.Induction.sum_ite_subtype_eq
import Submission.Work.Induction.indT_comp_indQh_eq_sum_indE
import Submission.Work.Induction.trace_indE

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- **Existence of the induced representation.**  For a finite-dimensional complex
-- representation `V` of a subgroup `H ≤ G`, there is a finite-dimensional complex
-- representation of `G` whose character is the induced function `indFun H V.character`.
-- (This is the "induced representation" whose character is the induced character; the
-- deliverable marked a bridge to `Mathlib`'s `Rep.ind` as optional, and `Rep.ind` is a
-- coinvariant model whose trace is not directly available, so we use the equivalent
-- fixed-functions model below.)
--
-- Suggested construction (`F := G → V` as a `ℂ`-vector space, `[Module.Finite ℂ F]`).
-- * For `h : H` let `Qh : F →ₗ[ℂ] F` be `(Qh f) x = V.ρ h (f (h⁻¹ * x))`.  These form an
--   action of `H` on `F` (`Qh ∘ Qh' = Q(hh')`), so `Q := (Nat.card H : ℂ)⁻¹ • ∑_{h : H} Qh` is
--   a projection whose range is `W := {f | ∀ h x, f (h * x) = V.ρ h (f x)}`: use
--   `Qh ∘ Q = Q` (reindexing the sum) to get `Q ∘ Q = Q`, i.e. `LinearMap.IsProj (range Q) Q`.
-- * Define `T : G →ₗ[ℂ] (F →ₗ[ℂ] F)`-style family `(T g f) x = f (x * g)`; it is a monoid
--   homomorphism (`T g ∘ T g' = T (g * g')`, so `g ↦ T g` *is* a `Representation ℂ G F`).
--   Each `T g` commutes with every `Qh` (both sides give `ρ h (f (h⁻¹ * x * g))`), hence with
--   `Q`, and therefore restricts to the submodule `W = range Q`, giving
--   `ρW : Representation ℂ G W` and `FDRep.of ρW` (`W` is finite dimensional as a submodule of
--   the finite dimensional `F`).
-- * Character: `(FDRep.of ρW).character g = trace_W (T g|_W) = trace_F (T g ∘ Q)`, because
--   `T g ∘ Q = ι_W ∘ (T g|_W) ∘ Q` and `Q ∘ ι_W = id_W`, so the cyclic invariance of the trace
--   (`LinearMap.trace_comp_cycle`, together with `LinearMap.IsProj.codRestrict`) applies.  Then
--   `trace_F (T g ∘ Q) = (Nat.card H : ℂ)⁻¹ * ∑_{h : H} trace_F (T g ∘ Qh)`.
-- * `T g ∘ Qh = ∑_{y : G} E y` where `(E y f) x = if x = h * y * g⁻¹ then V.ρ h (f y) else 0`;
--   each `E y` is the composite
--   `F --(evaluation at y)--> V --(V.ρ h)--> V --(insertion at h * y * g⁻¹)--> F`, so
--   `LinearMap.trace_comp_cycle` gives `trace_F (E y) = trace_V (V.ρ h) = V.character h` when
--   `h * y * g⁻¹ = y`, and `0` otherwise.  Summing over `h` and `y` yields
--   `(Nat.card H : ℂ)⁻¹ * ∑_{y : y * g * y⁻¹ ∈ H} V.character (y * g * y⁻¹)`, which is
--   `indFun H V.character g` by definition.

-- **The trace of `indT V g ∘ indQh V h`.**  Decomposing `indT V g ∘ indQh V h` into the rank-one
-- pieces `indE V h g y` (`Work.Induction.indT_comp_indQh_eq_sum_indE`) and applying
-- `Work.Induction.trace_indE` to each.
theorem trace_indT_comp_indQh {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (V : FDRep ℂ H) (g : G) (h : H) :
    LinearMap.trace ℂ (G → V) ((indT V g).comp (indQh V h)) =
      ∑ y : G, (if (h : G) = y * g * y⁻¹ then V.character h else 0) := by
  rw [indT_comp_indQh_eq_sum_indE, map_sum]
  exact Finset.sum_congr rfl (fun y _ => trace_indE V h g y)

-- **The trace of `indT V g ∘ indQ`.**  `indQ` is the average of the `indQh V h`, so by linearity
-- of the trace and of composition the trace of `indT V g ∘ indQ` is the average of the traces of
-- the `indT V g ∘ indQh V h`.
theorem trace_indT_comp_indQ {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (V : FDRep ℂ H) (g : G) :
    LinearMap.trace ℂ (G → V) ((indT V g).comp (indQ V)) =
      (Nat.card H : ℂ)⁻¹ * ∑ h : H,
        LinearMap.trace ℂ (G → V) ((indT V g).comp (indQh V h)) := by
  unfold indQ
  rw [LinearMap.comp_smul, comp_sum_eq V, map_smul, map_sum]
  simp [smul_eq_mul]

-- **The character of the fixed-functions model.**  Combining
-- * `LinearMap.IsProj` character identity `Work.Induction.trace_indTW` (the character of the
--   restriction to `indW V` is the trace of `indT V g ∘ indQ` on `G → V`),
-- * `Work.Induction.trace_indT_comp_indQ` and `Work.Induction.trace_indT_comp_indQh` (reducing to
--   the traces of the `indT V g ∘ indQh V h` and then to `V.character`),
-- * `Finset.sum_comm` (interchanging the sums over `H` and `G`), and
-- * `Work.Induction.sum_ite_subtype_eq` (collapsing the sum over `H` to a single term),
-- we recognise the defining formula of `Work.Induction.indFun`.
theorem character_indRhoV {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (V : FDRep ℂ H) (g : G) :
    Representation.character (indRhoV V) g = indFun H V.character g := by
  have hsum : (∑ h : H,
        LinearMap.trace ℂ (G → V) ((indT V g).comp (indQh V h))) =
      ∑ y : G, (if hy : y * g * y⁻¹ ∈ H then V.character ⟨y * g * y⁻¹, hy⟩ else 0) := by
    rw [Finset.sum_congr rfl (fun h _ => trace_indT_comp_indQh V g h), Finset.sum_comm]
    exact Finset.sum_congr rfl
      (fun y _ => sum_ite_subtype_eq V.character (y * g * y⁻¹))
  rw [Representation.character, indRhoV_apply, trace_indTW, trace_indT_comp_indQ, hsum]
  rfl

theorem exists_fdRep_of_indFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (V : FDRep ℂ H) : ∃ W : FDRep ℂ G, W.character = Work.Induction.indFun H V.character := by
  obtain ⟨W, hW⟩ := exists_fdRep_of_representation (indRhoV V)
  exact ⟨W, hW.trans (funext (character_indRhoV V))⟩

end Work.Induction
