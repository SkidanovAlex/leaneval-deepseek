import Mathlib
import Submission.Work.SSGRoute.classField_exists_ramified
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFT.Ideles.globalCFT_totallyDisconnectedSpace_unityIdeles
import Submission.NK.GlobalCFT.Ideles.globalCFT_unityIdeles_isCompact
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionIntegers_iInf_maximalIdeal_pow_eq_bot
import Submission.NK.GlobalCFT.LocalField.Topology
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup
import Submission.Work.SSGRoute.PTW.archDefs
import Submission.Work.SSGRoute.PTW.compact_connected_abelian_pow_surjective
import Submission.Work.SSGRoute.PTW.compactSpace_ker_abs
import Submission.Work.SSGRoute.PTW.abs_ideleClassGroup_pow_surjective
import Submission.Work.SSGRoute.PTW.mem_all_open_index_p_iff_mem_closure_pthPowers
import Submission.Work.SSGRoute.PTW.ideleClassGroup_quotient_instances
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-power criterion in the idèle class group

An element of `C_K = 𝕀 K ⧸ Kˣ` which lies in every open subgroup of index `p` is a `p`-th power.

The proof splits by the identity component `D := C_K⁰`:

* **(B) quotient step.**  Every open index-`p` subgroup of `C_K` contains `D`
  (`connectedComponentOfOne_le_of_isOpen_subgroup`), so the hypothesis descends to the quotient
  `C_K ⧸ D`.  That quotient is compact Hausdorff and totally disconnected
  (`ideleClassGroup_quotient_instances`), and `mem_all_open_index_p_iff_mem_closure_pthPowers`
  (a compact abelian group) shows that an element of the quotient lying in every open index-`p`
  subgroup lies in the closure of the `p`-th powers, which in a compact group is the set of `p`-th
  powers itself.  Lifting gives `x = y ^ p * g` with `g ∈ D` — see
  `ssg_exists_pow_mul_connectedComponentOfOne`.
* **(A) divisibility of `D`.**  `D` is `p`-divisible: with a continuous multiplicative section
  `archSec w₀` of the content map `|·| : C_K →* ℝˣ` at an infinite place, the retraction
  `φ z = z · archSec w₀ (|z|)⁻¹` identifies `D` with `ℝ_{>0} × H`, where
  `H = D ⊓ ker |·|` is the image of the connected `D`, hence compact connected abelian; a compact
  connected abelian group is divisible (`compact_connected_abelian_pow_surjective`) and `ℝ_{>0}`
  is `p`-divisible (`pos_units_pow_surjective`) — see
  `ssg_connectedComponentOfOne_pow_surjective`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.SSGRoute.PTW

open NK.GlobalCFT

/-! ## (A): the identity component of `C_K` is `p`-divisible -/

/-- **The content of an idèle class is positive.** -/
theorem ssg_abs_val_pos (K : Type) [Field K] [NumberField K] (z : IdeleClassGroup K) :
    0 < ((IdeleClassGroup.abs K z : ℝˣ) : ℝ) := by
  obtain ⟨a, rfl⟩ := IdeleClassGroup.mk_surjective K z
  rw [IdeleClassGroup.abs_mk]
  exact idele_abs_pos K a

/-- **The content `C_K →* ℝˣ` is continuous.** -/
theorem ssg_continuous_abs (K : Type) [Field K] [NumberField K] :
    Continuous (IdeleClassGroup.abs K) := by
  refine (QuotientGroup.isQuotientMap_mk (N := Idele.principalSubgroup K)).continuous_iff.mpr ?_
  have h : (⇑(IdeleClassGroup.abs K) ∘ (QuotientGroup.mk : Idele K → IdeleClassGroup K))
      = ⇑(Idele.abs K) := by
    funext a
    simpa only [Function.comp_apply, IdeleClassGroup.mk_apply, QuotientGroup.mk'_apply] using
      (IdeleClassGroup.abs_mk (K := K) a)
  rw [h]
  exact IdeleClassGroup.continuous_abs_aux

/-- **The idèle class group is Hausdorff.** -/
theorem ssg_t2Space_ideleClassGroup (K : Type) [Field K] [NumberField K] :
    T2Space (IdeleClassGroup K) := by
  rw [IsTopologicalGroup.t2Space_iff_one_closed]
  rw [← (QuotientGroup.isQuotientMap_mk (N := Idele.principalSubgroup K)).isClosed_preimage]
  have h : (QuotientGroup.mk ⁻¹' ({1} : Set (IdeleClassGroup K)))
      = (Idele.principalSubgroup K : Set (Idele K)) := by
    ext a
    rw [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq_one_iff]
    rfl
  rw [h]
  exact NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed

/-- **Divisibility of the identity component.**  An element of the identity component `C_K⁰` of the
idèle class group is a `p`-th power.

The content retraction `φ z = z · archSec w₀ (|z|)⁻¹` sends the connected group `C_K⁰` onto
`H = C_K⁰ ⊓ ker |·|`, which is therefore compact connected abelian, hence divisible
(`compact_connected_abelian_pow_surjective`); the content direction is handled by the divisibility
of `ℝ_{>0}` (`pos_units_pow_surjective`). -/
theorem ssg_connectedComponentOfOne_pow_surjective
    (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact (Nat.Prime p)]
    (x : NK.GlobalCFT.IdeleClassGroup K)
    (hx : x ∈ Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) :
    ∃ y : NK.GlobalCFT.IdeleClassGroup K, y ^ p = x := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  have hcont : Continuous (IdeleClassGroup.abs K) := ssg_continuous_abs K
  haveI : T2Space (IdeleClassGroup K) := ssg_t2Space_ideleClassGroup K
  -- the compact connected subgroup `H = C_K⁰ ⊓ ker |·|`
  set H : Subgroup (IdeleClassGroup K) :=
    Subgroup.connectedComponentOfOne (IdeleClassGroup K) ⊓ (IdeleClassGroup.abs K).ker with hH
  -- the retraction `z ↦ z * archSec |z|⁻¹`
  set φ : IdeleClassGroup K → IdeleClassGroup K := fun z =>
    z * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z)))⁻¹ with hφ
  have hφcont : Continuous φ := by
    show Continuous fun z : IdeleClassGroup K =>
      z * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z)))⁻¹
    refine Continuous.mul continuous_id ?_
    exact ((QuotientGroup.continuous_mk (N := Idele.principalSubgroup K)).comp
      ((continuous_archSec K w₀).comp hcont)).inv
  -- `φ` maps `C_K⁰` into `H`
  have hφmem : ∀ z ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K), φ z ∈ H := by
    intro z hz
    have hzpos : 0 < ((IdeleClassGroup.abs K z : ℝˣ) : ℝ) := ssg_abs_val_pos K z
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z))
          ∈ Subgroup.connectedComponentOfOne (IdeleClassGroup K) :=
        mk_archSec_mem_connectedComponentOfOne K w₀ _ hzpos
      exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ h1)
    · show IdeleClassGroup.abs K
        (z * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K z)))⁻¹) = 1
      rw [map_mul, map_inv, IdeleClassGroup.abs_mk, abs_archSec K w₀ hzpos, mul_inv_cancel]
  -- `H` is the image of the connected set `C_K⁰`
  have hHpre : IsPreconnected ((H : Set (IdeleClassGroup K))) := by
    have himg : (H : Set (IdeleClassGroup K)) =
        φ '' (Subgroup.connectedComponentOfOne (IdeleClassGroup K) : Set (IdeleClassGroup K)) := by
      ext w
      constructor
      · intro hw
        obtain ⟨hwcc, hwker⟩ := Subgroup.mem_inf.mp hw
        refine ⟨w, hwcc, ?_⟩
        have hw1 : IdeleClassGroup.abs K w = 1 := MonoidHom.mem_ker.mp hwker
        show w * (IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K w)))⁻¹ = w
        rw [hw1, archSec_one, map_one, inv_one, mul_one]
      · rintro ⟨a, ha, rfl⟩
        exact hφmem a ha
    rw [himg]
    exact (isPreconnected_connectedComponent (x := (1 : IdeleClassGroup K))).image φ
      hφcont.continuousOn
  have hHconn : ConnectedSpace ↥H := by
    haveI : PreconnectedSpace ↥H := isPreconnected_iff_preconnectedSpace.mp hHpre
    exact ConnectedSpace.mk ⟨⟨1, H.one_mem⟩⟩
  haveI hHconnI : ConnectedSpace ↥H := hHconn
  -- `H` is compact
  have hkercompact : IsCompact
      (((IdeleClassGroup.abs K).ker : Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) :=
    isCompact_iff_compactSpace.mpr (compactSpace_ker_abs K)
  have hHclosed : IsClosed ((H : Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) := by
    have hker : IsClosed
        (((IdeleClassGroup.abs K).ker : Subgroup (IdeleClassGroup K)) :
          Set (IdeleClassGroup K)) := by
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage hcont
    have hcc : IsClosed
        ((Subgroup.connectedComponentOfOne (IdeleClassGroup K) :
          Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) := isClosed_connectedComponent
    rw [hH]
    exact hcc.inter hker
  haveI hHcompact : CompactSpace ↥H :=
    isCompact_iff_compactSpace.mp (hkercompact.of_isClosed_subset hHclosed inf_le_right)
  -- `H` is divisible
  have hHroot : ∀ j : ↥H, ∃ u : ↥H, u ^ p = j := fun j =>
    compact_connected_abelian_pow_surjective ↥H p (Fact.out : Nat.Prime p).ne_zero j
  -- the content direction
  obtain ⟨d, hdpos, hd⟩ := pos_units_pow_surjective p (Fact.out : Nat.Prime p).ne_zero
    (IdeleClassGroup.abs K x) (ssg_abs_val_pos K x)
  -- write `x = m * j` with `j ∈ H`
  set m : IdeleClassGroup K :=
    IdeleClassGroup.mk K (archSec K w₀ (IdeleClassGroup.abs K x)) with hm
  set j : IdeleClassGroup K := m⁻¹ * x with hj
  have hjH : j ∈ H := by
    rw [hj, mul_comm m⁻¹ x]
    exact hφmem x hx
  obtain ⟨u, hu⟩ := hHroot ⟨j, hjH⟩
  -- both factors are `p`-th powers
  have hfac1 : m = (IdeleClassGroup.mk K (archSec K w₀ d)) ^ p := by
    rw [hm, ← hd, archSec_pow K w₀ d hdpos p, map_pow]
  have hfac2 : j = (u : IdeleClassGroup K) ^ p := by
    have h := congrArg (fun w : ↥H => (w : IdeleClassGroup K)) hu
    simpa using h.symm
  have hx_eq : x = m * j := by
    rw [hj, mul_inv_cancel_left]
  refine ⟨IdeleClassGroup.mk K (archSec K w₀ d) * (u : IdeleClassGroup K), ?_⟩
  rw [mul_pow, ← hfac1, ← hfac2, ← hx_eq]

/-! ## (B): reduction modulo the identity component -/

/-- **Reduction to the identity component.**  An element of `C_K` lying in every open subgroup of
index `p` differs from a `p`-th power by an element of the identity component `C_K⁰`.

Indeed, every open index-`p` subgroup contains `C_K⁰`, so the hypothesis passes to the compact
Hausdorff quotient `C_K ⧸ C_K⁰`; there the `p`-th powers form a compact (hence closed) set, and the
`p`-power criterion for compact abelian groups
(`mem_all_open_index_p_iff_mem_closure_pthPowers`) applies. -/
theorem ssg_exists_pow_mul_connectedComponentOfOne
    (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact (Nat.Prime p)]
    (x : NK.GlobalCFT.IdeleClassGroup K)
    (hx : ∀ V : Subgroup (NK.GlobalCFT.IdeleClassGroup K), V.FiniteIndex →
      IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)) → V.index = p → x ∈ V) :
    ∃ y : NK.GlobalCFT.IdeleClassGroup K,
      ∃ g : Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K),
        x = y ^ p * g := by
  classical
  obtain ⟨hcomp, -⟩ := ideleClassGroup_quotient_instances K
  set N : Subgroup (IdeleClassGroup K) :=
    Subgroup.connectedComponentOfOne (IdeleClassGroup K) with hN
  haveI : CompactSpace (IdeleClassGroup K ⧸ N) := hcomp
  haveI : IsClosed (N : Set (IdeleClassGroup K)) := isClosed_connectedComponent
  -- the hypothesis descends to `C_K ⧸ C_K⁰`
  have hxq : ∀ U : Subgroup (IdeleClassGroup K ⧸ N), U.FiniteIndex →
      IsOpen (U : Set (IdeleClassGroup K ⧸ N)) → U.index = p →
      (QuotientGroup.mk' N x) ∈ U := by
    intro U _ hUopen hUidx
    have hcont : Continuous (QuotientGroup.mk' N : IdeleClassGroup K → IdeleClassGroup K ⧸ N) :=
      QuotientGroup.continuous_mk
    have hidx : (Subgroup.comap (QuotientGroup.mk' N) U).index = p := by
      rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hUidx]
    have hfin : (Subgroup.comap (QuotientGroup.mk' N) U).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by rw [hidx]; exact (Fact.out : p.Prime).ne_zero)
    have hmem := hx _ hfin (hUopen.preimage hcont) hidx
    rwa [Subgroup.mem_comap] at hmem
  -- the compact `p`-power criterion in the quotient
  have h1 := (mem_all_open_index_p_iff_mem_closure_pthPowers
    (IdeleClassGroup K ⧸ N) p (QuotientGroup.mk' N x)).mp hxq
  have hclosed : IsClosed {y : IdeleClassGroup K ⧸ N |
      ∃ z : IdeleClassGroup K ⧸ N, z ^ p = y} := by
    have hh : {y : IdeleClassGroup K ⧸ N | ∃ z : IdeleClassGroup K ⧸ N, z ^ p = y} =
        Set.range (fun z : IdeleClassGroup K ⧸ N => z ^ p) := rfl
    rw [hh]
    exact IsCompact.isClosed (isCompact_range (continuous_id.pow p))
  rw [hclosed.closure_eq] at h1
  obtain ⟨yq, hyq⟩ := h1
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N yq
  refine ⟨y, ⟨(y ^ p)⁻¹ * x, ?_⟩, ?_⟩
  · have h : (QuotientGroup.mk' N) ((y ^ p)⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, map_pow, hyq, inv_mul_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact h
  · show x = y ^ p * ((y ^ p)⁻¹ * x)
    rw [mul_inv_cancel_left]

/-! ## The `p`-power criterion -/

/-- **The `p`-power criterion in the idèle class group.**  An element of `C_K` which lies in every
open subgroup of index `p` is a `p`-th power.  By `Work.SSGRoute.classField_exists_ramified` and
`NK.GlobalCFT.index_normClassSubgroup_eq_finrank`, the open index-`p` subgroups are exactly the
norm groups `N_{L/K}C_L` of the cyclic extensions `L/K` of degree `p`, so the hypothesis reads
"`x` is a norm from every cyclic degree-`p` extension" — which is what node `E3` of
`DESIGN_PT.md` needs.

Proof sketch: `⊇` is immediate since `C_K/V ≅ ℤ/p` for `V` of index `p`.  For `⊆`, an element
lying in every open index-`p` subgroup lies in every open subgroup with quotient of exponent `p`;
in the Hausdorff quotient `C_K / closure(C_K^p)` — a compactly generated commutative group of
exponent `p` — a nonzero class is separated from `1` by a continuous character into `𝔽_p`, whose
kernel is then an open index-`p` subgroup.  Use the structure of `C_K`
(`C_K ≅ C_K^0 × ℤ^{r_1+r_2-1}` with `C_K^0` compact) to see that `C_K^p` is closed and that the
compact part has enough characters (Frattini subgroup of a compact abelian group = closure of the
`p`-th powers). -/
theorem mem_pthPower_of_all_open_index_p_subgroups
    (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    ∀ x : NK.GlobalCFT.IdeleClassGroup K,
      (∀ (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)), V.FiniteIndex →
        IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)) → V.index = p → x ∈ V) →
      ∃ y : NK.GlobalCFT.IdeleClassGroup K, y ^ p = x := by
  intro x hx
  obtain ⟨y, g, hg⟩ := ssg_exists_pow_mul_connectedComponentOfOne K p x hx
  obtain ⟨z, hz⟩ := ssg_connectedComponentOfOne_pow_surjective K p g g.2
  exact ⟨y * z, by rw [mul_pow, hz, ← hg]⟩

end Work.SSGRoute.PTW
