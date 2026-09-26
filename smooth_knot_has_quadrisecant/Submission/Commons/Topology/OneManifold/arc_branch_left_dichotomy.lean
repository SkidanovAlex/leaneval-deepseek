import Mathlib.Analysis.Normed.Order.Lattice

open Set
open scoped Topology
open Filter

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Topology.OneManifold

namespace ArcBranchLeft

/-- The open unit interval as a type. -/
abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

/-- The branch domain `(0,c₀)` as a type. -/
abbrev Left (c₀ : ℝ) : Type := {s : ℝ // s ∈ Set.Ioo (0 : ℝ) c₀}

/-- The tail of `ORI` at real coordinate `b` (points above `b`). -/
def Tail (b : ℝ) : Set ORI := {t : ORI | b < (t : ℝ)}

/-- A continuous injective real-coordinate map `(a,b) → (c,d)` is strictly
monotone (increasing or decreasing) in the coordinate sense. -/
theorem coord_strictMono_or_anti {a b c d : ℝ} (hab : a < b)
    (f : {x : ℝ // x ∈ Set.Ioo a b} → {y : ℝ // y ∈ Set.Ioo c d})
    (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    StrictMono (fun x : {x : ℝ // x ∈ Set.Ioo a b} => (f x : ℝ)) ∨
    StrictAnti (fun x : {x : ℝ // x ∈ Set.Ioo a b} => (f x : ℝ)) := by
  let g : ℝ → ℝ := fun x => if hx : x ∈ Set.Ioo a b then (f ⟨x, hx⟩ : ℝ) else 0
  have hg_agrees : ∀ z : {x : ℝ // x ∈ Set.Ioo a b}, g (z : ℝ) = (f z : ℝ) := by
    intro z
    change (if hx : (z : ℝ) ∈ Set.Ioo a b then (f ⟨(z : ℝ), hx⟩ : ℝ) else 0) = (f z : ℝ)
    rw [dif_pos z.2]
  have hg_cont : ContinuousOn g (Set.Ioo a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : (Set.Ioo a b).domRestrict g =
        fun z : {x : ℝ // x ∈ Set.Ioo a b} => (f z : ℝ) := by
      funext z
      exact hg_agrees z
    rw [h1]
    exact continuous_subtype_val.comp hf_cont
  have hg_inj : InjOn g (Set.Ioo a b) := by
    intro x hx y hy hxy
    unfold g at hxy
    rw [dif_pos hx, dif_pos hy] at hxy
    have heq : f ⟨x, hx⟩ = f ⟨y, hy⟩ := Subtype.ext hxy
    have hxye : (⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo a b}) = ⟨y, hy⟩ := hf_inj heq
    exact congrArg Subtype.val hxye
  have hmono_or := ContinuousOn.strictMonoOn_of_injOn_Ioo (α := ℝ) (δ := ℝ) hab hg_cont hg_inj
  rcases hmono_or with hmono | hanti
  · left
    intro x y hxy
    have hxylt : (x : ℝ) < (y : ℝ) := hxy
    have hlt : g (x : ℝ) < g (y : ℝ) := hmono x.2 y.2 hxylt
    rw [hg_agrees x, hg_agrees y] at hlt
    exact hlt
  · right
    intro x y hxy
    have hxylt : (x : ℝ) < (y : ℝ) := hxy
    have hlt : g (y : ℝ) < g (x : ℝ) := hanti x.2 y.2 hxylt
    rw [hg_agrees x, hg_agrees y] at hlt
    exact hlt

/-- Continuity of `a` at an interior coordinate `c` gives a real `ε` window:
points whose coordinate is within `ε` of `c` map into any given open
neighbourhood `U` of `a⟨c⟩`. -/
theorem exists_eps_of_continuousAt {X : Type*} [TopologicalSpace X]
    (a : ORI → X) (ha : Continuous a) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1)
    {U : Set X} (hU : IsOpen U) (haU : a ⟨c, ⟨hc₀, hc₁⟩⟩ ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ORI, (t : ℝ) ∈ Set.Ioo (c - ε) (c + ε) → a t ∈ U := by
  have hpre : a ⁻¹' U ∈ 𝓝 (⟨c, ⟨hc₀, hc₁⟩⟩ : ORI) :=
    ha.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds hU haU)
  have hcomap : 𝓝 (⟨c, ⟨hc₀, hc₁⟩⟩ : ORI) =
      Filter.comap (fun t : ORI => (t : ℝ)) (𝓝 c) := by
    simpa using ((Topology.IsEmbedding.subtypeVal
      (p := fun r : ℝ => r ∈ Set.Ioo (0 : ℝ) 1)).isInducing.nhds_eq_comap ⟨c, ⟨hc₀, hc₁⟩⟩)
  have hpre' : a ⁻¹' U ∈ Filter.comap (fun t : ORI => (t : ℝ)) (𝓝 c) := by
    simpa [hcomap] using hpre
  rcases (Filter.mem_comap.mp hpre') with ⟨V, hV, hVsub⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have hy : |(t : ℝ) - c| < ε := by
    apply abs_lt.mpr
    constructor <;> linarith [ht.1, ht.2]
  have htin : (t : ℝ) ∈ Metric.ball c ε := by
    simpa [Real.dist_eq] using hy
  have htV : (t : ℝ) ∈ V := hball htin
  exact hVsub htV

/-- In a Hausdorff space, lying in the closure of every open neighbourhood of
`p` forces equality with `p`. -/
theorem eq_of_forall_open_closure {X : Type*} [TopologicalSpace X] [T2Space X]
    {p z : X} (h : ∀ U : Set X, IsOpen U → p ∈ U → z ∈ closure U) : z = p := by
  by_contra hne
  rcases t2_separation hne with ⟨u, v, hu, hv, hzu, hpv, hdis⟩
  have hz : z ∈ closure v := h v hv hpv
  have hznot : z ∉ closure v := by
    intro hzc
    have hsub : v ⊆ uᶜ := by
      intro y hyv hyu
      exact Set.disjoint_left.mp hdis.symm hyv hyu
    have huc : IsClosed uᶜ := isClosed_compl_iff.mpr hu
    have hcl : closure v ⊆ uᶜ := by
      calc
        closure v ⊆ closure uᶜ := closure_mono hsub
        _ = uᶜ := IsClosed.closure_eq huc
    exact hcl hzc hzu
  exact hznot hz

end ArcBranchLeft

open ArcBranchLeft

/-- **arc branch dichotomy, left end**.  Let `a : (0,1) → X` be a continuous
arc and `f : (0,c₀) → (0,1)` an injective continuous reparametrization of a
branch of it.  If a point `z` off the arc lies in the closure of the image of
every tail `(u,c₀)` of the branch, then either `z` lies in the closure of
every right tail `(b,1)` of the whole arc, or the branch covers a right
neighbourhood `(0,δ)` of the left end `0` of the arc parameter interval. -/
theorem arc_branch_left_dichotomy {X : Type*} [TopologicalSpace X] [T2Space X]
    (a : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → X)
    (ha_cont : Continuous a)
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (z : X) (hz_out : z ∉ Set.range a)
    (f : {s : ℝ // s ∈ Set.Ioo (0 : ℝ) c₀} → {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1})
    (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    (hzcl : ∀ u : {s : ℝ // s ∈ Set.Ioo (0 : ℝ) c₀},
        z ∈ closure (a '' (f '' {t : {s : ℝ // s ∈ Set.Ioo (0 : ℝ) c₀} | (u : ℝ) < (t : ℝ)}))) :
    (∀ b : ℝ, 0 < b → b < 1 →
      z ∈ closure (a '' {t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} | b < (t : ℝ)})) ∨
    (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∃ s : {s : ℝ // s ∈ Set.Ioo (0 : ℝ) c₀}, (f s : ℝ) = t) := by
  classical
  let fval : Left c₀ → ℝ := fun s => (f s : ℝ)
  let J : Set ℝ := Set.range fval
  have hfval_cont : Continuous fval := by
    exact continuous_subtype_val.comp hf_cont
  have hJ01 : J ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro y hy
    rcases hy with ⟨s, hs⟩
    rw [← hs]
    exact (f s).2
  have hJne : J.Nonempty := by
    let s₀ : Left c₀ := ⟨c₀ / 2, by constructor <;> linarith⟩
    exact ⟨fval s₀, ⟨s₀, rfl⟩⟩
  have hJbddAbove : BddAbove J := ⟨1, fun y hy => le_of_lt (((hJ01 hy).2))⟩
  have hJbddBelow : BddBelow J := ⟨0, fun y hy => le_of_lt (((hJ01 hy).1))⟩
  have hJconn : IsConnected J := by
    haveI : ConnectedSpace (Left c₀) := isConnected_iff_connectedSpace.mp (isConnected_Ioo hc₀₀)
    have hJimg : IsConnected (fval '' (Set.univ : Set (Left c₀))) :=
      IsConnected.image isConnected_univ fval hfval_cont.continuousOn
    have hJJ : fval '' (Set.univ : Set (Left c₀)) = J := by
      ext y
      simp [J]
    rwa [← hJJ]
  let M : ℝ := sSup J
  let m : ℝ := sInf J
  have hMgt0 : 0 < M := by
    rcases hJne with ⟨w, hw⟩
    have hw01 : w ∈ Set.Ioo (0 : ℝ) 1 := hJ01 hw
    have hwM : w ≤ M := by
      dsimp [M]
      exact le_csSup hJbddAbove hw
    exact lt_of_lt_of_le hw01.1 hwM
  have hMle1 : M ≤ 1 := by
    dsimp [M]
    exact csSup_le hJne (fun y hy => le_of_lt (((hJ01 hy).2)))
  have hmge0 : 0 ≤ m := by
    dsimp [m]
    exact le_csInf hJne (fun y hy => le_of_lt (((hJ01 hy).1)))
  have hmlt1 : m < 1 := by
    rcases hJne with ⟨w, hw⟩
    have hw01 : w ∈ Set.Ioo (0 : ℝ) 1 := hJ01 hw
    have hmw : m ≤ w := by
      dsimp [m]
      exact csInf_le hJbddBelow hw
    exact lt_of_le_of_lt hmw hw01.2
  rcases coord_strictMono_or_anti (a := 0) (b := c₀) (c := 0) (d := 1) hc₀₀ f
      hf_cont hf_inj with hinc | hdec
  · -- increasing branch
    by_cases hM1 : M = 1
    · -- sup is 1 : z is a limit point of every right tail of the arc
      left
      intro b hb0 hb1
      have hbM : b < M := by rwa [hM1]
      rcases exists_lt_of_lt_csSup hJne hbM with ⟨v, hv, hbv⟩
      rcases hv with ⟨u, hu⟩
      have hfuv : (f u : ℝ) = v := by simpa [fval] using hu
      have hbz : z ∈ closure (a '' (f '' {t : Left c₀ | (u : ℝ) < (t : ℝ)})) := hzcl u
      have hsub : a '' (f '' {t : Left c₀ | (u : ℝ) < (t : ℝ)}) ⊆ a '' Tail b := by
        rintro x ⟨p, hp, hx⟩
        rcases hp with ⟨t, ht, hpt⟩
        have hpb : b < (p : ℝ) := by
          have hut : (u : ℝ) < (t : ℝ) := ht
          have hlt : (f u : ℝ) < (f t : ℝ) := hinc hut
          have hbflt : b < (f u : ℝ) := by
            calc
              b < v := hbv
              _ = fval u := hu.symm
              _ = (f u : ℝ) := by rfl
          calc
            b < (f u : ℝ) := hbflt
            _ < (f t : ℝ) := hlt
            _ = (p : ℝ) := by rw [← hpt]
        refine ⟨p, hpb, ?_⟩
        exact hx
      exact closure_mono hsub hbz
    · -- sup strictly below 1 : impossible (z would equal the arc point at sup)
      exfalso
      have hMlt1 : M < 1 := lt_of_le_of_ne hMle1 hM1
      have hzM : z = a ⟨M, ⟨hMgt0, hMlt1⟩⟩ := by
        exact eq_of_forall_open_closure (p := a ⟨M, ⟨hMgt0, hMlt1⟩⟩) (z := z) (by
          intro U hUopen haU
          rcases exists_eps_of_continuousAt a ha_cont hMgt0 hMlt1 hUopen haU with ⟨ε, hε, hεprop⟩
          have hbM : M - ε < M := by linarith
          rcases exists_lt_of_lt_csSup hJne hbM with ⟨v, hv, hMv⟩
          rcases hv with ⟨u, hu⟩
          have hbz : z ∈ closure (a '' (f '' {t : Left c₀ | (u : ℝ) < (t : ℝ)})) := hzcl u
          have hsub : a '' (f '' {t : Left c₀ | (u : ℝ) < (t : ℝ)}) ⊆ U := by
            rintro x ⟨p, hp, hx⟩
            rcases hp with ⟨t, ht, hpt⟩
            have hval : (f t : ℝ) ∈ Set.Ioo (M - ε) (M + ε) := by
              have hut : (u : ℝ) < (t : ℝ) := ht
              have hlt : (f u : ℝ) < (f t : ℝ) := hinc hut
              have hMflt : M - ε < (f u : ℝ) := by
                calc
                  M - ε < v := hMv
                  _ = fval u := hu.symm
                  _ = (f u : ℝ) := by rfl
              have hMt : M - ε < (f t : ℝ) := lt_trans hMflt hlt
              have hle : (f t : ℝ) ≤ M := by
                exact le_csSup hJbddAbove ⟨t, rfl⟩
              exact ⟨hMt, lt_of_le_of_lt hle (by linarith)⟩
            have hapU : a p ∈ U := by
              rw [← hpt]
              exact hεprop (f t) hval
            simpa [hx] using hapU
          exact closure_mono hsub hbz)
      exact hz_out ⟨⟨M, ⟨hMgt0, hMlt1⟩⟩, hzM.symm⟩
  · -- decreasing branch
    by_cases hm0 : m = 0
    · -- the branch covers a right neighbourhood `(0,M)` of `0`
      right
      refine ⟨M, hMgt0, ?_⟩
      intro t ht0 htM
      have hIJ : Set.Ioo (sInf J) (sSup J) ⊆ J :=
        IsConnected.Ioo_csInf_csSup_subset hJconn hJbddBelow hJbddAbove
      have htI : t ∈ Set.Ioo (sInf J) (sSup J) := by
        constructor
        · have hs0 : sInf J = 0 := by simpa [m] using hm0
          linarith
        · simpa [M] using htM
      rcases hIJ htI with ⟨s, hs⟩
      exact ⟨s, by simpa [fval] using hs⟩
    · -- inf strictly above 0 : impossible (z would equal the arc point at inf)
      exfalso
      have hmg0 : 0 < m := lt_of_le_of_ne hmge0 (Ne.symm hm0)
      have hzm : z = a ⟨m, ⟨hmg0, hmlt1⟩⟩ := by
        exact eq_of_forall_open_closure (p := a ⟨m, ⟨hmg0, hmlt1⟩⟩) (z := z) (by
          intro U hUopen haU
          rcases exists_eps_of_continuousAt a ha_cont hmg0 hmlt1 hUopen haU with ⟨ε, hε, hεprop⟩
          have hb : sInf J < m + ε := by
            dsimp [m]
            linarith
          rcases exists_lt_of_csInf_lt hJne hb with ⟨v, hv, hvm⟩
          rcases hv with ⟨u, hu⟩
          have hbz : z ∈ closure (a '' (f '' {t : Left c₀ | (u : ℝ) < (t : ℝ)})) := hzcl u
          have hsub : a '' (f '' {t : Left c₀ | (u : ℝ) < (t : ℝ)}) ⊆ U := by
            rintro x ⟨p, hp, hx⟩
            rcases hp with ⟨t, ht, hpt⟩
            have hval : (f t : ℝ) ∈ Set.Ioo (m - ε) (m + ε) := by
              have hut : (u : ℝ) < (t : ℝ) := ht
              have hlt : (f t : ℝ) < (f u : ℝ) := hdec hut
              have hflu : (f u : ℝ) < m + ε := by
                have hfv : (f u : ℝ) = v := by simpa [fval] using hu
                calc
                  (f u : ℝ) = v := hfv
                  _ < m + ε := hvm
              have hup : (f t : ℝ) < m + ε := lt_trans hlt hflu
              have hlo : m - ε < (f t : ℝ) := by
                have hmle : m ≤ (f t : ℝ) := by
                  simpa [m] using (csInf_le hJbddBelow ⟨t, rfl⟩)
                exact lt_of_lt_of_le (by linarith) hmle
              exact ⟨hlo, hup⟩
            have hapU : a p ∈ U := by
              rw [← hpt]
              exact hεprop (f t) hval
            simpa [hx] using hapU
          exact closure_mono hsub hbz)
      exact hz_out ⟨⟨m, ⟨hmg0, hmlt1⟩⟩, hzm.symm⟩

end Commons.Topology.OneManifold