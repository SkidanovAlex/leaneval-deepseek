import ChallengeDeps
import Submission.FinalAssembly
import Submission.Metric
import Submission.MetricConst
import Submission.LocalExt2
import Submission.UlU
import Mathlib

/-!
# Direction A interfaces: right/left geodesic extension (rigid statements)

Theorems: `Submission.geoRightExt` and `Submission.geoLeftExt`.

## Statements (they are exactly `FinalAssembly.GeoRightExt M` / `GeoLeftExt M`)

    theorem geoRightExt {E : Type*} ... [IsRiemannianManifold I M] [CompleteSpace M]
        [LocallyCompactSpace M] [ConnectedSpace M] : FinalAssembly.GeoRightExt M
    theorem geoLeftExt  {E : Type*} ... [IsRiemannianManifold I M] [CompleteSpace M]
        [LocallyCompactSpace M] [ConnectedSpace M] : FinalAssembly.GeoLeftExt M

Proof architecture, entirely metric after the two rigid ingredients:

* `Submission.local_extension` (LocalExt2): at every point `q` and speed `c > 0` there is
  `η > 0` such that any locally-linear `c`-curve with limit `q` at its right endpoint
  `b⁻` extends to `(a, b+η)`.
* `Submission.locallyLinear_ext_unique` (UlU): two locally-linear `c`-curves on the same
  interval `(a,β)` that agree on a left sub-interval agree everywhere (uniqueness of
  extensions).  This makes independently chosen extensions compatible.

Then a purely metric assembly (`rightExt_of_local_uniq`, no Riemannian hypotheses) proves
`GeoRightExt M` given any such "local extension" operation and uniqueness fact:

1. For `c = 0` the curve is constant on `(a,b)` (`Metric.IsLocLinear.eq_of_speed_zero`);
   extend constantly.
2. For `c > 0`: a curve `δ` on `(a,T)` is *extendable* (P `T`) iff it extends to a locally
   linear curve on `(a,T)` agreeing with `γ` on `(a,b)`.
   - `P` is downward closed (restrict), `P b` holds.
   - `P` is right-open: `P T` (with `b ≤ T`) gives the limit of an extension at `T⁻` in a
     complete space, hence `local_extension` pushes `P` to `P (T+η)`.
   - `P` is sup-closed: if `P` holds on all of `[b,T)`, the countable family
     `s n := T - (T-b)/(n+1)` has extensions which agree pairwise on overlaps (uniqueness),
     so they glue to an extension on `(a,T)`.
   - A standard interval/supremum argument then gives `P B` for every `B ≥ b`.
3. Choose, for each `t`, an extension at the endpoint `B t := max (b+1) (t+1) > b` and define
   `γR t` by it.  Uniqueness makes `γR` agree with every extension on its interval, so the
   windows of the chosen extensions give `IsLocLinRight a c γR`.

`geoLeftExt` is obtained from `geoRightExt` by time reflection
(`t ↦ γ(-t)` turns a left limit at `a⁺` into a right limit at `(-a)⁻`, and
`IsLocLinRight (-b)` turns into `IsLocLinLeft b` under negation).

Do NOT change the statements of `geoRightExt`/`geoLeftExt`; helper lemmas are free.  The final
file must contain no unfinished proofs and declare no new axioms.
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Filter Metric
open Bundle

namespace Submission

open LeanEval.Geometry

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

namespace Metric
namespace IsLocLinear

variable {M : Type*} [PseudoEMetricSpace M]

/-- Time reflection preserves local linearity: `u ↦ γ (-u)` is locally linear on `(-b,-a)`. -/
lemma reflect {a b : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : IsLocLinear a b c γ) :
    IsLocLinear (-b) (-a) c (fun u => γ (-u)) := by
  intro t₀ ht₀
  let t : ℝ := -t₀
  have ht : t ∈ Ioo a b := by
    constructor <;> dsimp [t] <;> linarith [ht₀.1, ht₀.2]
  rcases hγ t ht with ⟨δ, hδ, hwin⟩
  refine ⟨δ, hδ, ?_⟩
  intro s u hs hu
  have hsmem : -s ∈ Ioo (max a (t - δ)) (min b (t + δ)) := by
    constructor
    · have h1 : a < -s := by
        have hb : s < -a := by
          have hs2 : s < min (-a) (t₀ + δ) := hs.2
          exact lt_of_lt_of_le hs2 (min_le_left (-a) (t₀ + δ))
        linarith
      have h2 : t - δ < -s := by
        have hs1 : s < t₀ + δ := lt_of_lt_of_le hs.2 (min_le_right (-a) (t₀ + δ))
        dsimp [t]
        linarith
      exact max_lt h1 h2
    · have h1 : -s < b := by
        have hs1 : -b < s := lt_of_le_of_lt (le_max_left (-b) (t₀ - δ)) hs.1
        linarith
      have h2 : -s < t + δ := by
        have hs1 : t₀ - δ < s := lt_of_le_of_lt (le_max_right (-b) (t₀ - δ)) hs.1
        dsimp [t]
        linarith
      exact lt_min h1 h2
  have humem : -u ∈ Ioo (max a (t - δ)) (min b (t + δ)) := by
    constructor
    · have h1 : a < -u := by
        have hb : u < -a := by
          have hu2 : u < min (-a) (t₀ + δ) := hu.2
          exact lt_of_lt_of_le hu2 (min_le_left (-a) (t₀ + δ))
        linarith
      have h2 : t - δ < -u := by
        have hu1 : u < t₀ + δ := lt_of_lt_of_le hu.2 (min_le_right (-a) (t₀ + δ))
        dsimp [t]
        linarith
      exact max_lt h1 h2
    · have h1 : -u < b := by
        have hu1 : -b < u := lt_of_le_of_lt (le_max_left (-b) (t₀ - δ)) hu.1
        linarith
      have h2 : -u < t + δ := by
        have hu1 : t₀ - δ < u := lt_of_le_of_lt (le_max_right (-b) (t₀ - δ)) hu.1
        dsimp [t]
        linarith
      exact lt_min h1 h2
  have hdst := hwin (-s) (-u) hsmem humem
  have harg : |(-u) - (-s)| = |u - s| := by
    rw [abs_sub_comm]
    congr 1
    ring
  calc
    edist (γ (-s)) (γ (-u)) = (c : ℝ≥0∞) * ENNReal.ofReal |(-u) - (-s)| := hdst
    _ = (c : ℝ≥0∞) * ENNReal.ofReal |u - s| := by rw [harg]

end IsLocLinear
end Metric

/-- Reflection of a left limit `a⁺` to a right limit `(-a)⁻` of the time-reversed curve. -/
lemma tendsto_neg_Ioi {M : Type*} [TopologicalSpace M] {a : ℝ} {γ : ℝ → M} {p : M}
    (h : Tendsto γ (𝓝[Ioi a] a) (𝓝 p)) :
    Tendsto (fun u : ℝ => γ (-u)) (𝓝[Iio (-a)] (-a)) (𝓝 p) := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.neg ℝ
  have hset : ⇑e '' Iio (-a) = Ioi a := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy' : y < -a := hy
      change a < -y
      linarith
    · intro hx
      refine ⟨-x, ?_, ?_⟩
      · have hx' : a < x := hx
        change -x < -a
        linarith
      · simp [e]
  have hpt : ⇑e (-a) = a := by
    simp [e]
  have hmap : Filter.map e (𝓝[Iio (-a : ℝ)] (-a)) = 𝓝[Ioi a] a := by
    rw [e.isEmbedding.map_nhdsWithin_eq, hset, hpt]
  have hγe0 : Tendsto (γ ∘ e) (𝓝[Iio (-a : ℝ)] (-a)) (𝓝 p) := by
    unfold Filter.Tendsto
    rw [← Filter.map_map, hmap]
    exact h
  simpa [e, Function.comp_def] using hγe0

/-- The right-extension assembly: purely metric.  Given a local extension operation (for
positive speeds) and uniqueness of extensions, every locally linear curve on `(a,b)` with a
limit at `b⁻` extends to a right-locally-linear curve on `(a,∞)`. -/
theorem rightExt_of_local_uniq {M : Type*} [EMetricSpace M] [CompleteSpace M]
    (hLE : ∀ (q : M) (c : NNReal), 0 < c →
      ∃ η > 0, ∀ (a b : ℝ), a < b → ∀ (γ : ℝ → M),
        Metric.IsLocLinear a b c γ →
        Tendsto γ (𝓝[Iio b] b) (𝓝 q) →
        ∃ γR : ℝ → M, (∀ t ∈ Ioo a b, γR t = γ t) ∧ Metric.IsLocLinear a (b + η) c γR)
    (hLU : ∀ (a b β : ℝ) (c : NNReal) (γ₁ γ₂ : ℝ → M),
        a < b → b ≤ β →
        Metric.IsLocLinear a β c γ₁ → Metric.IsLocLinear a β c γ₂ →
        (∀ t ∈ Ioo a b, γ₁ t = γ₂ t) → ∀ t ∈ Ioo a β, γ₁ t = γ₂ t) :
    FinalAssembly.GeoRightExt M := by
  classical
  intro a b c γ hab hγ hp
  by_cases hc0 : c = 0
  · let m : ℝ := (a + b) / 2
    have hmI : m ∈ Ioo a b := by
      constructor <;> dsimp [m] <;> linarith
    have hγ0 : Metric.IsLocLinear a b 0 γ := by simpa [hc0] using hγ
    let γR : ℝ → M := fun _ => γ m
    refine ⟨γR, ?_, ?_⟩
    · intro t ht
      dsimp [γR]
      exact Metric.IsLocLinear.eq_of_speed_zero (M := M) hγ0 hmI ht
    · rw [hc0]
      intro t₀ ht₀
      refine ⟨1, by norm_num, ?_⟩
      intro s t hs ht h1 h2
      dsimp [γR]
      simp
  · have hc : 0 < c := by
      exact pos_iff_ne_zero.mpr hc0
    let P : ℝ → Prop := fun T => ∃ δ : ℝ → M,
      Metric.IsLocLinear a T c δ ∧ ∀ t ∈ Ioo a b, δ t = γ t
    have hPb : P b := by
      refine ⟨γ, ?_, ?_⟩
      · exact hγ
      · intro t ht; rfl
    have hP_mono : ∀ {T T' : ℝ}, P T → T' ≤ T → P T' := by
      intro T T' hPT hT'T
      rcases hPT with ⟨δ, hlin, hag⟩
      refine ⟨δ, ?_, ?_⟩
      · exact Metric.IsLocLinear.restrict hlin (le_refl a) hT'T
      · exact hag
    have hP_open : ∀ {T : ℝ}, b ≤ T → P T → ∃ η > 0, P (T + η) := by
      intro T hbT hPT
      rcases hPT with ⟨δ, hlin, hag⟩
      have haT : a < T := lt_of_lt_of_le hab hbT
      rcases Metric.IsLocLinear.exists_tendsto_nhdsWithin_Iio (M := M) hlin haT with ⟨q, hq⟩
      rcases hLE q c hc with ⟨η, hη0, hηspec⟩
      refine ⟨η, hη0, ?_⟩
      rcases hηspec a T haT δ hlin hq with ⟨γR, hagR, hlinR⟩
      refine ⟨γR, hlinR, ?_⟩
      intro t ht
      have htT : t < T := lt_of_lt_of_le ht.2 hbT
      rw [hagR t ⟨ht.1, htT⟩, hag t ht]
    have hP_sup : ∀ {T : ℝ}, b < T → (∀ t : ℝ, b ≤ t → t < T → P t) → P T := by
      intro T hbT hAll
      let s : ℕ → ℝ := fun n => T - (T - b) / (n + 1)
      have hs_b : ∀ n : ℕ, b ≤ s n := by
        intro n
        dsimp [s]
        have hpos : 0 ≤ (T - b) / (n + 1) := by positivity
        have hle : (T - b) / (n + 1) ≤ T - b := by
          have hnn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have hnn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
          have htb0 : 0 ≤ T - b := by linarith
          rw [div_le_iff₀ hnn]
          nlinarith [mul_le_mul_of_nonneg_left hnn1 htb0]
        linarith
      have hs_lt : ∀ n : ℕ, s n < T := by
        intro n
        dsimp [s]
        have hpos : 0 < (T - b) / (n + 1) := by positivity
        linarith
      have hPw : ∀ n : ℕ, ∃ δ : ℝ → M,
          Metric.IsLocLinear a (s n) c δ ∧ ∀ t ∈ Ioo a b, δ t = γ t := by
        intro n
        exact hAll (s n) (hs_b n) (hs_lt n)
      let δw : ℕ → ℝ → M := fun n => Classical.choose (hPw n)
      have hδw_lin : ∀ n : ℕ, Metric.IsLocLinear a (s n) c (δw n) := by
        intro n
        exact (Classical.choose_spec (hPw n)).1
      have hδw_ag : ∀ n : ℕ, ∀ t ∈ Ioo a b, δw n t = γ t := by
        intro n
        exact (Classical.choose_spec (hPw n)).2
      have hδw_agree : ∀ n m : ℕ, ∀ t ∈ Ioo a (min (s n) (s m)), δw n t = δw m t := by
        intro n m t ht
        have hβ : b ≤ min (s n) (s m) := le_min (hs_b n) (hs_b m)
        have hlin_n : Metric.IsLocLinear a (min (s n) (s m)) c (δw n) :=
          Metric.IsLocLinear.restrict (hδw_lin n) (le_refl a) (min_le_left _ _)
        have hlin_m : Metric.IsLocLinear a (min (s n) (s m)) c (δw m) :=
          Metric.IsLocLinear.restrict (hδw_lin m) (le_refl a) (min_le_right _ _)
        exact hLU a b (min (s n) (s m)) c (δw n) (δw m) hab hβ hlin_n hlin_m
          (fun u hu => (hδw_ag n u hu).trans (hδw_ag m u hu).symm) t ht
      have hcover : ∀ t : ℝ, t < T → ∃ n : ℕ, t < s n := by
        intro t ht
        have hTt : 0 < T - t := sub_pos.mpr ht
        have hTb0 : 0 < T - b := sub_pos.mpr hbT
        have hratio0 : 0 ≤ (T - b) / (T - t) := by positivity
        rcases exists_nat_gt ((T - b) / (T - t)) with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        dsimp [s]
        have hNN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have hN1 : (N : ℝ) < (N : ℝ) + 1 := by linarith
        have hratio : (T - b) / (T - t) < (N : ℝ) + 1 := lt_of_lt_of_le hN hN1.le
        rw [div_lt_iff₀ hTt] at hratio
        have hmain : (T - b) / ((N : ℝ) + 1) < T - t := by
          rw [div_lt_iff₀ hNN]
          nlinarith
        linarith
      let γstar : ℝ → M := fun t => if ht : t < T then δw (Classical.choose (hcover t ht)) t else δw 0 t
      have hγstar_eq : ∀ n : ℕ, ∀ t ∈ Ioo a (s n), γstar t = δw n t := by
        intro n t ht
        dsimp [γstar]
        have htT : t < T := lt_trans ht.2 (hs_lt n)
        rw [dif_pos htT]
        exact hδw_agree (Classical.choose (hcover t htT)) n t ⟨ht.1,
          lt_min (Classical.choose_spec (hcover t htT)) ht.2⟩
      refine ⟨γstar, ?_, ?_⟩
      · intro t₀ ht₀
        rcases hcover t₀ ht₀.2 with ⟨n, ht₀n⟩
        have ht₀in : t₀ ∈ Ioo a (s n) := ⟨ht₀.1, ht₀n⟩
        rcases hδw_lin n t₀ ht₀in with ⟨δ0, hδ0, hwin0⟩
        let ε : ℝ := min δ0 ((s n - t₀) / 2)
        have hε : 0 < ε := lt_min hδ0 (div_pos (sub_pos.mpr ht₀n) (by norm_num))
        refine ⟨ε, hε, ?_⟩
        intro u v hu hv
        have hu_lt_sn : u < s n := by
          have hu1 : u < t₀ + ε := lt_of_lt_of_le hu.2 (min_le_right T (t₀ + ε))
          have hεle : ε ≤ (s n - t₀) / 2 := min_le_right δ0 ((s n - t₀) / 2)
          nlinarith
        have hv_lt_sn : v < s n := by
          have hv1 : v < t₀ + ε := lt_of_lt_of_le hv.2 (min_le_right T (t₀ + ε))
          have hεle : ε ≤ (s n - t₀) / 2 := min_le_right δ0 ((s n - t₀) / 2)
          nlinarith
        have hu_in : u ∈ Ioo (max a (t₀ - δ0)) (min (s n) (t₀ + δ0)) := by
          constructor
          · have huL : t₀ - δ0 < u := by
              have hu1 : t₀ - ε < u := lt_of_le_of_lt (le_max_right a (t₀ - ε)) hu.1
              have hεle : ε ≤ δ0 := min_le_left δ0 ((s n - t₀) / 2)
              linarith
            exact max_lt (lt_of_le_of_lt (le_max_left a (t₀ - ε)) hu.1) huL
          · exact lt_min hu_lt_sn (by
              have hu1 : u < t₀ + ε := lt_of_lt_of_le hu.2 (min_le_right T (t₀ + ε))
              have hεle : ε ≤ δ0 := min_le_left δ0 ((s n - t₀) / 2)
              linarith)
        have hv_in : v ∈ Ioo (max a (t₀ - δ0)) (min (s n) (t₀ + δ0)) := by
          constructor
          · have hvL : t₀ - δ0 < v := by
              have hv1 : t₀ - ε < v := lt_of_le_of_lt (le_max_right a (t₀ - ε)) hv.1
              have hεle : ε ≤ δ0 := min_le_left δ0 ((s n - t₀) / 2)
              linarith
            exact max_lt (lt_of_le_of_lt (le_max_left a (t₀ - ε)) hv.1) hvL
          · exact lt_min hv_lt_sn (by
              have hv1 : v < t₀ + ε := lt_of_lt_of_le hv.2 (min_le_right T (t₀ + ε))
              have hεle : ε ≤ δ0 := min_le_left δ0 ((s n - t₀) / 2)
              linarith)
        have hu_eq : γstar u = δw n u := hγstar_eq n u ⟨lt_of_le_of_lt (le_max_left a (t₀ - ε)) hu.1, hu_lt_sn⟩
        have hv_eq : γstar v = δw n v := hγstar_eq n v ⟨lt_of_le_of_lt (le_max_left a (t₀ - ε)) hv.1, hv_lt_sn⟩
        rw [hu_eq, hv_eq]
        exact hwin0 u v hu_in hv_in
      · intro t ht
        have htT : t < T := lt_trans ht.2 hbT
        dsimp [γstar]
        rw [dif_pos htT]
        exact hδw_ag (Classical.choose (hcover t htT)) t ht
    have hPB : ∀ B : ℝ, b ≤ B → P B := by
      intro B hbB
      by_cases hBb : B = b
      · subst B
        exact hPb
      · have hbB' : b < B := lt_of_le_of_ne hbB (Ne.symm hBb)
        by_contra hnot
        let S : Set ℝ := {t : ℝ | b ≤ t ∧ t ≤ B ∧ P t}
        have hS_nonempty : S.Nonempty := ⟨b, by
          refine ⟨le_rfl, hbB, hPb⟩⟩
        have hS_bdd : BddAbove S := ⟨B, by
          intro x hx; exact hx.2.1⟩
        let Tstar : ℝ := sSup S
        have hbTstar : b ≤ Tstar := le_csSup hS_bdd (by exact ⟨le_rfl, hbB, hPb⟩)
        have hTstarB : Tstar ≤ B := csSup_le hS_nonempty (by intro x hx; exact hx.2.1)
        have hbelow : ∀ t : ℝ, b ≤ t → t < Tstar → P t := by
          intro t hbt htT
          have hExs : ∃ s : ℝ, s ∈ S ∧ t < s := by
            by_contra h
            push Not at h
            have : Tstar ≤ t := csSup_le hS_nonempty h
            linarith
          rcases hExs with ⟨s, hsS, hts⟩
          exact hP_mono hsS.2.2 (le_of_lt hts)
        have hmain : False := by
          rcases lt_or_eq_of_le hbTstar with hbTstar_lt | hTstareqb
          · have hPTstar : P Tstar := hP_sup hbTstar_lt hbelow
            rcases lt_or_eq_of_le hTstarB with hTstarBlt | hTstarBeq
            · rcases hP_open hbTstar hPTstar with ⟨η, hη0, hPη⟩
              let T₁ : ℝ := min (Tstar + η) B
              have hbT₁ : b ≤ T₁ := le_min (by linarith) hbB
              have hT₁B : T₁ ≤ B := min_le_right _ _
              have hT₁Tη : T₁ ≤ Tstar + η := min_le_left _ _
              have hP₁ : P T₁ := hP_mono hPη hT₁Tη
              have hT₁S : T₁ ∈ S := ⟨hbT₁, hT₁B, hP₁⟩
              have hle : T₁ ≤ sSup S := le_csSup hS_bdd hT₁S
              have hT₁gt : Tstar < T₁ := by
                dsimp [T₁]
                exact lt_min (by linarith) hTstarBlt
              linarith
            · exact hnot (by rwa [hTstarBeq] at hPTstar)
          · subst Tstar
            rcases hP_open (le_refl b) hPb with ⟨η, hη0, hPη⟩
            let T₁ : ℝ := min (b + η) B
            have hbT₁ : b ≤ T₁ := le_min (by linarith) hbB
            have hT₁B : T₁ ≤ B := min_le_right _ _
            have hT₁Tη : T₁ ≤ b + η := min_le_left _ _
            have hP₁ : P T₁ := hP_mono hPη hT₁Tη
            have hT₁S : T₁ ∈ S := ⟨hbT₁, hT₁B, hP₁⟩
            have hle : T₁ ≤ sSup S := le_csSup hS_bdd hT₁S
            have hT₁gt : b < T₁ := by
              dsimp [T₁]
              exact lt_min (by linarith) hbB'
            linarith
        exact False.elim hmain
    let Bf : ℝ → ℝ := fun t => max (b + 1) (t + 1)
    have hBf_b : ∀ t : ℝ, b ≤ Bf t := by
      intro t
      dsimp [Bf]
      have h1 : b ≤ b + 1 := by linarith
      exact le_trans h1 (le_max_left _ _)
    have hBf_gt : ∀ t : ℝ, t < Bf t := by
      intro t
      dsimp [Bf]
      have h1 : t < t + 1 := by linarith
      exact lt_of_lt_of_le h1 (le_max_right _ _)
    let δT : (T : ℝ) → (hb : b ≤ T) → ℝ → M := fun T hb => Classical.choose (hPB T hb)
    have hδT_lin : ∀ (T : ℝ) (hb : b ≤ T), Metric.IsLocLinear a T c (δT T hb) := by
      intro T hb
      exact (Classical.choose_spec (hPB T hb)).1
    have hδT_ag : ∀ (T : ℝ) (hb : b ≤ T), ∀ t ∈ Ioo a b, δT T hb t = γ t := by
      intro T hb
      exact (Classical.choose_spec (hPB T hb)).2
    let γR : ℝ → M := fun t => δT (Bf t) (hBf_b t) t
    refine ⟨γR, ?_, ?_⟩
    · intro t ht
      dsimp [γR]
      exact hδT_ag (Bf t) (hBf_b t) t ht
    · intro t₀ ht₀
      let T₀ : ℝ := Bf t₀
      have hbT₀ : b ≤ T₀ := hBf_b t₀
      have ht₀T₀ : t₀ < T₀ := hBf_gt t₀
      have ht₀in : t₀ ∈ Ioo a T₀ := ⟨ht₀, ht₀T₀⟩
      rcases hδT_lin T₀ hbT₀ t₀ ht₀in with ⟨δ0, hδ0, hwin0⟩
      let ε : ℝ := min δ0 ((T₀ - t₀) / 2)
      have hε : 0 < ε := lt_min hδ0 (div_pos (sub_pos.mpr ht₀T₀) (by norm_num))
      refine ⟨ε, hε, ?_⟩
      intro s t hs_a ht_a hsε htε
      have hsT₀ : s < T₀ := by
        have h2 : |s - t₀| < (T₀ - t₀) / 2 := lt_of_lt_of_le hsε (min_le_right δ0 ((T₀ - t₀) / 2))
        have h3 : s - t₀ < (T₀ - t₀) / 2 := lt_of_le_of_lt (le_abs_self (s - t₀)) h2
        nlinarith
      have htT₀ : t < T₀ := by
        have h2 : |t - t₀| < (T₀ - t₀) / 2 := lt_of_lt_of_le htε (min_le_right δ0 ((T₀ - t₀) / 2))
        have h3 : t - t₀ < (T₀ - t₀) / 2 := lt_of_le_of_lt (le_abs_self (t - t₀)) h2
        nlinarith
      have hγR_eq : ∀ u : ℝ, a < u → u < T₀ → γR u = δT T₀ hbT₀ u := by
        intro u hau huT₀
        dsimp [γR]
        let B1 : ℝ := Bf u
        have hb1 : b ≤ B1 := hBf_b u
        have huB1 : u < B1 := hBf_gt u
        let m : ℝ := min B1 T₀
        have hβ : b ≤ m := le_min hb1 hbT₀
        have hlin1 : Metric.IsLocLinear a m c (δT B1 hb1) :=
          Metric.IsLocLinear.restrict (hδT_lin B1 hb1) (le_refl a) (min_le_left _ _)
        have hlin2 : Metric.IsLocLinear a m c (δT T₀ hbT₀) :=
          Metric.IsLocLinear.restrict (hδT_lin T₀ hbT₀) (le_refl a) (min_le_right _ _)
        have hEq : δT B1 hb1 u = δT T₀ hbT₀ u :=
          hLU a b m c (δT B1 hb1) (δT T₀ hbT₀) hab hβ hlin1 hlin2
            (fun w hw => (hδT_ag B1 hb1 w hw).trans (hδT_ag T₀ hbT₀ w hw).symm)
            u ⟨hau, lt_min huB1 huT₀⟩
        exact hEq
      have hγs : γR s = δT T₀ hbT₀ s := hγR_eq s hs_a hsT₀
      have hγt : γR t = δT T₀ hbT₀ t := hγR_eq t ht_a htT₀
      rw [hγs, hγt]
      have hsW : s ∈ Ioo (max a (t₀ - δ0)) (min T₀ (t₀ + δ0)) := by
        constructor
        · have h1 : |s - t₀| < δ0 := lt_of_lt_of_le hsε (min_le_left δ0 ((T₀ - t₀) / 2))
          have hL : t₀ - δ0 < s := by linarith [(abs_lt.mp h1).1]
          exact max_lt hs_a hL
        · exact lt_min hsT₀ (by
            have h1 : |s - t₀| < δ0 := lt_of_lt_of_le hsε (min_le_left δ0 ((T₀ - t₀) / 2))
            exact by linarith [(abs_lt.mp h1).2])
      have htW : t ∈ Ioo (max a (t₀ - δ0)) (min T₀ (t₀ + δ0)) := by
        constructor
        · have h1 : |t - t₀| < δ0 := lt_of_lt_of_le htε (min_le_left δ0 ((T₀ - t₀) / 2))
          have hL : t₀ - δ0 < t := by linarith [(abs_lt.mp h1).1]
          exact max_lt ht_a hL
        · exact lt_min htT₀ (by
            have h1 : |t - t₀| < δ0 := lt_of_lt_of_le htε (min_le_left δ0 ((T₀ - t₀) / 2))
            exact by linarith [(abs_lt.mp h1).2])
      exact hwin0 s t hsW htW

/-- Given the right interface, the left interface follows by time reflection. -/
theorem geoLeftExt_of_geoRightExt {M : Type*} [EMetricSpace M]
    (hGR : FinalAssembly.GeoRightExt M) : FinalAssembly.GeoLeftExt M := by
  intro a b c γ hab hγ hp
  let γ' : ℝ → M := fun u => γ (-u)
  have hI : -b < -a := by linarith
  have hγ' : Metric.IsLocLinear (-b) (-a) c γ' := by
    dsimp [γ']
    exact Metric.IsLocLinear.reflect hγ
  rcases hp with ⟨p, hptend⟩
  have hp' : ∃ p : M, Tendsto γ' (𝓝[Iio (-a)] (-a)) (𝓝 p) := by
    refine ⟨p, ?_⟩
    dsimp [γ']
    exact tendsto_neg_Ioi hptend
  rcases hGR (-b) (-a) c γ' hI hγ' hp' with ⟨δ, hEq', hLinR⟩
  let γL : ℝ → M := fun t => δ (-t)
  refine ⟨γL, ?_, ?_⟩
  · intro t ht
    dsimp [γL]
    have hneg : -t ∈ Ioo (-b) (-a) := by constructor <;> linarith [ht.1, ht.2]
    have hE := hEq' (-t) hneg
    dsimp [γ'] at hE
    simpa using hE
  · intro t₀ ht₀
    have hneg₀ : -b < -t₀ := by linarith
    rcases hLinR (-t₀) hneg₀ with ⟨ε, hε, hwin⟩
    refine ⟨ε, hε, ?_⟩
    intro s t hs ht h1 h2
    have hsneg : -b < -s := by linarith
    have htneg : -b < -t := by linarith
    have h1n : |(-s) - (-t₀)| < ε := by
      have hstep : (-s) - (-t₀) = -(s - t₀) := by ring
      rw [hstep, abs_neg]
      exact h1
    have h2n : |(-t) - (-t₀)| < ε := by
      have hstep : (-t) - (-t₀) = -(t - t₀) := by ring
      rw [hstep, abs_neg]
      exact h2
    have hd := hwin (-s) (-t) hsneg htneg h1n h2n
    dsimp [γL]
    have harg : |(-t) - (-s)| = |t - s| := by
      rw [abs_sub_comm]
      congr 1
      ring
    calc
      edist (δ (-s)) (δ (-t)) = (c : ℝ≥0∞) * ENNReal.ofReal |(-t) - (-s)| := hd
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by rw [harg]

theorem geoRightExt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [LocallyCompactSpace M] [ConnectedSpace M] :
    FinalAssembly.GeoRightExt M := by
  classical
  have hLE : ∀ (q : M) (c : NNReal), 0 < c →
      ∃ η > 0, ∀ (a b : ℝ), a < b → ∀ (γ : ℝ → M),
        Metric.IsLocLinear a b c γ →
        Tendsto γ (𝓝[Iio b] b) (𝓝 q) →
        ∃ γR : ℝ → M, (∀ t ∈ Ioo a b, γR t = γ t) ∧ Metric.IsLocLinear a (b + η) c γR := by
    intro q c hc
    exact local_extension (I := I) (M := M) q c hc
  have hLU : ∀ (a b β : ℝ) (c : NNReal) (γ₁ γ₂ : ℝ → M),
      a < b → b ≤ β →
      Metric.IsLocLinear a β c γ₁ → Metric.IsLocLinear a β c γ₂ →
      (∀ t ∈ Ioo a b, γ₁ t = γ₂ t) → ∀ t ∈ Ioo a β, γ₁ t = γ₂ t := by
    intro a b β c γ₁ γ₂ hab hbβ hγ₁ hγ₂ hag
    exact locallyLinear_ext_unique (I := I) (M := M) hab hbβ hγ₁ hγ₂ hag
  exact rightExt_of_local_uniq (M := M) hLE hLU

theorem geoLeftExt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [LocallyCompactSpace M] [ConnectedSpace M] :
    FinalAssembly.GeoLeftExt M := by
  classical
  exact geoLeftExt_of_geoRightExt (M := M) (geoRightExt (E := E) (I := I) (M := M))

end Submission
