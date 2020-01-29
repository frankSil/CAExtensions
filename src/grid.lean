import utils
import data.vector data.list data.int.basic tactic.omega data.fin
       tactic.linarith tactic.apply

open utils

section grids

open list

class relative_grid (α : Type*) :=
  (carrier  : Type)
  (rows     : α → ℕ)
  (cols     : α → ℕ)
  (nonempty : Πg, rows g * cols g > 0)
  (data     : Πg, fin (rows g) → fin (cols g) → carrier)

class grid (α : Type*) extends relative_grid α :=
  (bl : α → point)

section grid_defs

variables {α : Type*} [grid α] (g : α)

open grid relative_grid

notation `|`:max x `|`:0 := int.nat_abs x

def size := rows g * cols g

attribute [simp]
lemma size_eq_rows_mul_cols : size g = rows g * cols g := rfl

def tr (bl : point) (r c : ℕ) : point :=
  ⟨bl.x + c, bl.y + r⟩

attribute [simp]
def grid_rows := rows g

attribute [simp]
def grid_cols := cols g

attribute [simp]
def gbl := bl g

def gtr := tr (bl g) (rows g) (cols g)

def tl : point := ⟨(bl g).x, (bl g).y + rows g⟩

def br : point := ⟨(bl g).x + cols g, (bl g).y⟩

lemma expand_gbl : gbl g = bl g := by simp

lemma expand_gtr : gtr g = ⟨(bl g).x + cols g, (bl g).y + rows g⟩ :=
  by simp [gtr, tr]

lemma blx_eq_tlx {g : α} : (bl g).x = (tl g).x := by simp [bl, tl]

lemma brx_eq_trx {g : α} : (br g).x = (gtr g).x := by simp [br, expand_gtr]

lemma bly_eq_bry {g : α} : (bl g).y = (br g).y := by simp [br]

lemma tly_eq_try {g : α} : (tl g).y = (gtr g).y := by simp [expand_gtr, tl]

structure bounding_box := (p₁ : point) (p₂ : point) (h : p₁ ↗ p₂)

def bbox_str : bounding_box → string
  | ⟨p₁, p₂, _⟩ := "<(" ++ to_string p₁ ++ ", " ++ to_string p₂ ++ ")>"

instance : has_to_string bounding_box := ⟨bbox_str⟩

instance : has_repr bounding_box := ⟨bbox_str⟩

def bb_eq (bb₁ bb₂ : bounding_box) := bb₁.p₁ = bb₂.p₂ ∧ bb₁.p₂ = bb₂.p₂

instance dec_eq_bb {bb₁ bb₂} : decidable (bb_eq bb₁ bb₂) :=
  by simp [bb_eq]; apply_instance

instance : decidable_eq bounding_box :=
  λbb₁ bb₂, begin
              cases bb₁, cases bb₂,
              simp, apply_instance
            end

def points_of_box (bb : bounding_box) : point × point := ⟨bb.p₁, bb.p₂⟩

def rows_of_box (bb : bounding_box) : ℕ :=
  |bb.p₂.y - bb.p₁.y|
 
def cols_of_box (bb : bounding_box) : ℕ :=
  |bb.p₂.x - bb.p₁.x|

def bb_size (bb : bounding_box) := rows_of_box bb * cols_of_box bb

private def data_option (g : α) (x y : ℕ) :=
  if h : y < cols g
  then if h₁ : x < rows g
       then some $ data g ⟨x, h₁⟩ ⟨y, h⟩
       else none
  else none

end grid_defs

section grid_lemmas

open grid relative_grid function

variables {α : Type*} [grid α] {g : α}

private theorem data_data_option {x y : ℕ}
  (h₁ : y < rows g) (h₂ : x < cols g) :
  some (data g ⟨y, h₁⟩ ⟨x, h₂⟩) = data_option g y x :=
  by unfold data_option; repeat { rw dif_pos; try { simp [is_bounded, h.2] } };
     simpa

lemma rows_of_box_pos {bb : bounding_box} : rows_of_box bb > 0 :=
let ⟨⟨_, y₁⟩, ⟨_, y₂⟩, h⟩ := bb in
begin
  simp only [rows_of_box, gt_from_lt], simp [grid_bounded_iff] at h,
  rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg]; omega
end

lemma cols_of_box_pos {bb : bounding_box} : cols_of_box bb > 0 :=
let ⟨⟨x₁, _⟩, ⟨x₂, _⟩, h⟩ := bb in
begin
  simp only [cols_of_box, gt_from_lt], simp [grid_bounded_iff] at h,
  rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg]; omega
end

lemma rows_pos : 0 < rows g :=
  (gt_and_gt_of_mul_gt (nonempty g)).1

lemma cols_pos : 0 < cols g :=
  (gt_and_gt_of_mul_gt (nonempty g)).2

lemma abs_rows_pos : 0 < |rows g| := rows_pos

lemma abs_cols_pos : 0 < |cols g| := cols_pos

lemma coe_rows_pos : (0 : ℤ) < ↑(rows g) := by simp [rows_pos]

lemma coe_cols_pos {g : α} : (0 : ℤ) < ↑(cols g) := by simp [cols_pos]

lemma idx_div_cols_bounded {n} (h : n < size g) :
  (bl g).y + ↑n / ↑(cols g) < (gtr g).y :=
begin
  simp [expand_gtr, gt_from_lt] at *, norm_cast,
  rw mul_comm at h,
  replace h := nat.div_lt_of_lt_mul h,
  linarith
end

lemma idx_mod_cols_bounded {n : ℕ} :
  (bl g).x + ↑n % ↑(cols g) < (gtr g).x :=
  by simp [expand_gtr]; exact int.mod_lt_of_pos _ coe_cols_pos

lemma grid_is_bounding_box : bl g ↗ gtr g :=
let ⟨h₁, h₂⟩ := gt_and_gt_of_mul_gt (nonempty g) in
  grid_bounded_iff.2 ⟨
    by simpa [expand_gtr],
    by simpa [expand_gtr]
  ⟩

structure relative_point (g : α) :=
  (x : fin (rows g))
  (y : fin (cols g))

def relative_point_str (g : α) : relative_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "]"

instance : has_to_string (relative_point g) :=
  ⟨relative_point_str g⟩

instance : has_repr (relative_point g) :=
  ⟨relative_point_str g⟩

structure grid_point (g : α) :=
  (y : bounded (bl g).y (gtr g).y)
  (x : bounded (bl g).x (gtr g).x)

def grid_point_str (g : α) : grid_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "] - "
              ++ to_string (bl g)

instance : has_to_string (grid_point g) := ⟨grid_point_str g⟩

instance : has_repr (grid_point g) := ⟨grid_point_str g⟩

lemma blgy_lt_trgy : (bl g).y < (gtr g).y :=
  by simp [expand_gtr, rows_pos]

lemma gblx_lt_gtrx : (gbl g).x < (gtr g).x :=
  expand_gtr g ▸ expand_gbl g ▸ lt_add_of_pos_right _ coe_cols_pos

private lemma grid_rows_eq_try_sub_bly :
  grid_rows g = |(gtr g).y - (bl g).y| :=
  by simp [expand_gtr]

lemma rows_eq_try_sub_bly :
  rows g = |(gtr g).y - (bl g).y| := grid_rows_eq_try_sub_bly

lemma rows_eq_try_sub_bly' :
  ↑(rows g) = (gtr g).y - (bl g).y := by simp [gtr, tr]

private lemma grid_cols_eq_trx_sub_blx
  : grid_cols g = |((gtr g).x - (bl g).x)| :=
  by simp [expand_gtr]

lemma cols_eq_trx_sub_blx
  : cols g = |((gtr g).x - (bl g).x)| := grid_cols_eq_trx_sub_blx

def relpoint_of_gpoint {g : α} (p : grid_point g) : relative_point g :=
    ⟨
      ⟨|p.y.1 - (bl g).y|,  
       begin
         rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, ⟨y, ⟨yl, yu⟩⟩⟩, simp,
         have eq₁ : x + -(bl g).y ≥ 0, by linarith,
         have eq₂ : (gtr g).y - (bl g).y ≥ 0, by simp [expand_gtr]; linarith,
         rw [
           ← int.coe_nat_lt_coe_nat_iff, rows_eq_try_sub_bly,
           int.nat_abs_of_nonneg eq₁, int.nat_abs_of_nonneg eq₂
         ],
         linarith
       end
      ⟩,
      ⟨|p.x.1 - (bl g).x|,
       have h : p.x.1 - (tl g).x ≥ 0,
         from le_sub_iff_add_le.2 (by simp [tl, p.x.2.1]),
       ((int.coe_nat_lt_coe_nat_iff _ _).1 $
        (int.nat_abs_of_nonneg h).symm ▸
        begin
          let uby := p.x.2.2,
          simp only [expand_gtr] at uby,
          simp only [tl],
          linarith
        end)
      ⟩
    ⟩

def gpoint_of_relpoint {g : α} (p : relative_point g) : grid_point g :=
  ⟨
    ⟨(bl g).y + p.x.1,
      ⟨
        by simp [tl, expand_gtr],
        by rcases p with ⟨⟨_, h⟩, _⟩; simp only [tl, expand_gtr, h]; linarith
      ⟩
    ⟩,
    ⟨(bl g).x + p.y.1,
      ⟨
        by simp [tl],
        by rcases p with ⟨⟨_, _⟩, ⟨_, h⟩⟩; simp only [tl, expand_gtr, h]; linarith
      ⟩
    ⟩
  ⟩

lemma relpoint_gpoint_id {g : α} {p : grid_point g} :
  gpoint_of_relpoint (relpoint_of_gpoint p) = p :=
begin
  rcases p with ⟨⟨x, ⟨hx₁, _⟩⟩, ⟨y, ⟨hy₁, _⟩⟩⟩,
  simp [relpoint_of_gpoint, gpoint_of_relpoint, -sub_eq_add_neg],
  have : x - (bl g).y ≥ 0, by linarith,
  have : y - (bl g).x ≥ 0, by linarith,
  split; rw int.nat_abs_of_nonneg; try { simp }; assumption
end

lemma gpoint_relpoint_id {g : α} {p : relative_point g} :
  relpoint_of_gpoint (gpoint_of_relpoint p) = p :=
  by cases p with x y; simp [gpoint_of_relpoint, relpoint_of_gpoint]

def prod_of_rel_point {g : α} (rp : relative_point g) := (rp.x, rp.y)

def prod_of_grid_point {g : α} (ap : grid_point g) := (ap.x, ap.y)

def grid_point_of_prod {g : α}
  (p : bounded (bl g).x (gtr g).x ×
       bounded (bl g).y (gtr g).y) : grid_point g :=
  ⟨p.snd, p.fst⟩

def grid_point_of_prod' {g : α}
  (p : bounded (bl g).y (gtr g).y ×
       bounded (bl g).x (gtr g).x) : grid_point g :=
  ⟨p.fst, p.snd⟩

def abs_data (g : α) (gp : grid_point g) :=
  let rp := relpoint_of_gpoint gp in
    (data g) rp.x rp.y

lemma try_lt_bly : (gbl g).y < (gtr g).y :=
  (grid_bounded_iff.1 grid_is_bounding_box).2

private lemma bounded_establishes_bounds {a b : ℤ}
  (h : a < b) (x : bounded 0 ( |b - a| )) :
  a ≤ a + ↑x ∧ a + ↑x < b :=
have xpos : ↑x ≥ 0, from positive_bounded _,
have xmax : ↑x < |b - a|, from bounded_lt _,
  ⟨
    by apply le_add_of_nonneg_right; unfold coe,
    begin
      unfold_coes at *,
      rw add_comm,
      rw [← int.coe_nat_lt, int.nat_abs_of_nonneg, lt_sub_iff_add_lt] at xmax,
      exact xmax,
      {
        simp [ge_from_le],
        rw [
          ← sub_eq_add_neg, ← add_le_add_iff_right a,
          zero_add, sub_add_cancel
        ],
        exact int.le_of_lt h,
      }
    end
  ⟩

end grid_lemmas

end grids

section grid_impls

structure vec_grid (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (data : vector α (r * c))

structure vec_grid₀ (α : Type) extends vec_grid α :=
  (o : point)

structure fgrid₀ (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (o : point)
  (data : bounded o.y (o.y + r) → bounded o.x (o.x + c) → α)

end grid_impls

section grid_instances

open relative_grid grid

lemma data_not_empty {α : Type} {g : vec_grid₀ α} : ¬empty_list g.data.to_list :=
assume contra,
begin
  simp [empty_list] at contra,
  have contra₁ := contra.symm,
  rw [list_empty_iff_len, vector.to_list_length] at contra₁,
  rcases g with ⟨⟨_, _, h,_⟩, _⟩,
  linarith
end

lemma linearize_array {x y r c : ℕ}
  (xb : x < c) (yb : y < r) : y * c + x < r * c :=
have h₁ : y * c < r * c, by apply mul_lt_mul yb; omega,
have h₂ : ∃n, nat.succ y + n = r, from nat_le_dest yb,
let ⟨n, h₂⟩ := h₂ in
  by rw [← h₂, right_distrib, nat.succ_mul, add_assoc]; linarith

def rel_point_to_fin {α : Type} [grid α] {g : α}
  (p : relative_point g) : fin (size g) :=
  ⟨p.x * cols g + p.y, linearize_array p.y.2 p.x.2⟩

def grid_point_to_fin {α : Type} [grid α] {g : α}
  (p : grid_point g) : fin (size g) := rel_point_to_fin (relpoint_of_gpoint p)

lemma expand_grid_point_to_fin {α : Type} [grid α] {g : α}
  (p : grid_point g) : grid_point_to_fin p =
  ⟨|p.y.1 - (bl g).y| * cols g + |p.x.1 - (bl g).x|,
  linearize_array
    begin
      rcases p with ⟨_, ⟨y, ⟨_, yu⟩⟩⟩,
      simp only [tl], rw ← int.coe_nat_lt_coe_nat_iff,
      have : y - (grid.bl g).x ≥ 0, by rw [ge_from_le]; linarith,
      rw int.nat_abs_of_nonneg this,
      simp [expand_gtr] at yu,
      linarith
    end
    begin
      rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, _⟩,
      simp only [tl], rw ← int.coe_nat_lt_coe_nat_iff,
      have : x - (bl g).y ≥ 0, by linarith,
      rw [int.nat_abs_of_nonneg this, rows_eq_try_sub_bly'],
      linarith
    end⟩ :=
  by simp [grid_point_to_fin, relpoint_of_gpoint, rel_point_to_fin]; unfold_coes

instance rg_vec_grid {α : Type} :
  relative_grid (vec_grid α) := {
    carrier  := α,
    rows     := λg, g.r,
    cols     := λg, g.c,
    nonempty := λg, g.h,
    data     :=
    λg y x,
      g.data.nth ⟨
        y.1 * g.c + x.1,
        linearize_array x.2 y.2
      ⟩    
}

instance rg_vec_grid₀ {α : Type} :
  relative_grid (vec_grid₀ α) := {
    carrier  := α,
    rows     := λg, g.r,
    cols     := λg, g.c,
    nonempty := λg, g.h,
    data     :=
    λg y x,
      g.data.nth ⟨
        y.1 * g.c + x.1,
        linearize_array x.2 y.2
      ⟩   
}

private lemma absolute_bounds {o : ℤ} {r : ℕ}
                              (x : fin r) : o + ↑x < o + ↑r :=
  by simp; cases x; unfold_coes; simpa

instance rg_fgrid₀ {α : Type} :
  relative_grid (fgrid₀ α) := {
    carrier  := α,
    rows     := λg, g.r,
    cols     := λg, g.c,
    nonempty := λg, g.h,
    data     := λg y x,
      g.data ⟨g.o.y + y, ⟨by simp, absolute_bounds _⟩⟩
             ⟨g.o.x + x, ⟨by simp, absolute_bounds _⟩⟩
}

instance ag_vec_agrid₀ {α : Type} :
  grid (vec_grid₀ α) := {
    bl := λg, g.o
  }

instance ag_fgrid₀ {α : Type} :
  grid (fgrid₀ α) := {
    bl := λg, g.o
  }

def point_of_grid_point {α : Type*} [grid α] {g : α} : grid_point g → point
  | ⟨b₁, b₂⟩ := ⟨b₂, b₁⟩

instance point_grid_point_coe {α : Type*} [grid α] (g : α) :
  has_coe (grid_point g) point := ⟨point_of_grid_point⟩

end grid_instances

section finite_grid

open list int function

section spec

open grid relative_grid

variables {α : Type} {ag : vec_grid₀ α} {fg : fgrid₀ α}

lemma coe_rows_pos_a : ↑ag.r > (0 : ℤ) :=
  by change ag.r with (rows ag); simp [gt_from_lt, rows_pos]

lemma coe_rows_pos_f : ↑fg.r > (0 : ℤ) :=
  by change fg.r with (rows fg); simp [gt_from_lt, rows_pos]

lemma coe_cols_pos_a : ↑ag.c > (0 : ℤ) :=
  by change ag.c with (cols ag); simp [gt_from_lt, cols_pos]

lemma coe_cols_pos_f : ↑fg.c > (0 : ℤ) :=
  by change fg.c with (cols fg); simp [gt_from_lt, cols_pos]

end spec

variables {α : Type*} [grid α] (g : α)

def grp (a b row : ℤ) : list point :=
  map (uncurry point.mk) $ zip (range_pure a b)
                               (repeat row ( |b - a| ))

private lemma expand_grp {a b r} (h : a < b) :
  grp a b r =
  ⟨a, r⟩ :: grp (a + 1) b r :=
begin
  conv_lhs { simp only [grp] },
  rw range_pure_next h,
  have : |b - a| ≥ 1, from nat_abs_ge_one_of_lt h,
  rw repeat_more this, simp [-sub_eq_add_neg],
  exact ⟨
    by simp [uncurry],
    by simp [grp, -sub_eq_add_neg, abs_minus_plus h]
  ⟩
end

private lemma expand_grp_g {g : α} :
  grp (gbl g).x (gtr g).x (gtr g).y =
  ⟨(gbl g).x, (gtr g).y⟩ ::
  grp ((gbl g).x + 1) (gtr g).x (gtr g).y :=
begin
  simp only [grp],
  have h : range_pure ((gbl g).x) ((gtr g).x) =
           (gbl g).x ::
           range_pure (((gbl g).x) + 1) ((gtr g).x),
    from range_pure_next (grid_bounded_iff.1 grid_is_bounding_box).1,
  rw h,
  have h₁ : repeat ((gtr g).y)
                   ( |(gtr g).x - (gbl g).x| ) =
            (gtr g).y :: repeat (gtr g).y ( |(gtr g).x - (gbl g).x| - 1),
    {
      simp only [expand_gbl], apply repeat_more,
      rw ← cols_eq_trx_sub_blx,
      exact abs_cols_pos
    },
  simp only [map, h₁, zip_cons_cons],
  exact ⟨
    by simp [uncurry],
    by rw abs_minus_plus;
       exact (grid_bounded_iff.1 grid_is_bounding_box).1
  ⟩
end

private lemma grp_empty_iff {a b r} :
  empty_list (grp a b r) ↔ b ≤ a :=
  ⟨
    assume h, begin
      by_cases contra : a < b,
        {rw expand_grp at h, cases h, exact contra},
        {exact le_of_not_lt contra}
    end,
    assume h, begin
      unfold grp,
      have : range_pure a b = [],
        by unfold1 range_pure; exact if_neg (not_lt_of_le h),
      simp [zip_nil_left, empty_list, this]
    end
  ⟩

lemma grp_empty_iff' {a b r} : grp a b r = [] ↔ (b ≤ a) :=
begin
  split; intros h,
    {rw ← grp_empty_iff, simp [empty_list, h.symm]},
    {
      have : empty_list (grp a b r), from grp_empty_iff.2 h,
      simp only [empty_list] at this,
      exact this.symm
    }
end

lemma grp_nil_iff {x y} : grp x x y = [] :=
  have h : empty_list (grp x x y), from grp_empty_iff.2 (le_refl _),
  h.symm

lemma in_grp_second {a b r} {p} (h₁ : p ∈ grp a b r) :
  p.y = r :=
begin
  cases p with px py, simp only [point.y] at *,
  revert h₁,
  induction eq : grp a b r with hd tl generalizing a; intros,
    {cases h₁},
    {
      by_cases h : a < b,
        {
          rw expand_grp h at eq, injection eq with eq₁ eq₂,
          rw mem_cons_iff at h₁, cases h₁ with h₁ h₁,
            {cc},
            {
              by_cases h₂ : a + 1 < b,
                {exact ih eq₂ h₁,},
                {
                  rw not_lt at h₂, 
                  rw grp_empty_iff'.2 h₂ at eq₂, subst eq₂,
                  cases h₁
                }
            }
        },
        {rw not_lt at h, rw grp_empty_iff'.2 h at eq, cases eq}
    }
end

lemma in_grp_iff {a b r} {c : point} (h₀ : a < b) :
  c ∈ grp a b r ↔ is_bounded a b c.x ∧ c.y = r :=
begin
  split; intros h,
    {
      split, unfold grp at h, simp [-sub_eq_add_neg, uncurry] at h,
      rcases h with ⟨a₁, b₂, ⟨h₁, h₂⟩⟩,
      have : a₁ ∈ range_pure a b, from pair_in_zip_l h₁,
      rw in_range_pure_iff at this,
      cases c, cc, exact in_grp_second h
    },
    {
      cases c with x y, simp only [point.x, point.y] at *,
      unfold is_bounded at h,
      rcases h with ⟨⟨h, h₁⟩, h₂⟩, simp [grp, -sub_eq_add_neg, uncurry],
      use x, use y, split,
        {
          apply in_zip_of_and, intros, subst h₂, 
          exact eq_of_mem_repeat H,
          rw in_range_pure_iff, unfold is_bounded, exact ⟨h, h₁⟩,
          rw length_repeat, rw range_length_pure (int.le_of_lt h₀)
        },
        {simp}
    }
end

lemma notin_grp_of_lt {p : point} {a b r : ℤ} (h : p.x < a) :
  p ∉ grp a b r := 
begin
  cases p with px py, simp only [point.x] at *,  
  induction eq : grp a b r with hd tl generalizing a,
    {intros contra, cases contra},
    {
      by_cases h₁ : a < b,
        {
          rw expand_grp h₁ at eq, injection eq with eq₁ eq₂, clear eq,
          intros contra, cases contra,
            {subst eq₁, subst eq₂, cases contra, linarith},
            {
              by_cases h₂ : a + 1 < b,
                {
                  specialize @ih (a + 1) (by linarith) eq₂,
                  contradiction
                },
                {
                  rw not_lt at h₂, rw grp_empty_iff'.2 h₂ at eq₂,
                  subst eq₂, cases contra
                }
            }
        },
        {rw not_lt at h₁, rw grp_empty_iff'.2 h₁ at eq, cases eq}
    }
end

lemma nodup_grp {a b r} : nodup (grp a b r) :=
begin
  induction eq : grp a b r with hd tl generalizing a,
    {exact nodup_nil},
    {
      by_cases h : a < b,
        {
          rw expand_grp h at eq, injection eq with eq₁ eq₂,
          rw nodup_cons, split,
            {
              rw [← eq₂, ← eq₁],
              apply notin_grp_of_lt,
              simp only [point.x], linarith
            },
            {exact ih eq₂}
        },
        {rw not_lt at h, rw grp_empty_iff'.2 h at eq, cases eq}
    }
end

open function

private lemma grp_bounds {a b row : ℤ} :
  ∀{c : point}, c ∈ grp a b row →
    is_bounded a b c.x ∧ is_bounded row (row + 1) c.y :=
assume c h,
begin
  simp [grp] at h,
  rcases h with ⟨a₁, ⟨b₁, ⟨h₂, h₃⟩⟩⟩,
  have h₄ : a₁ ∈ range_pure a b, from pair_in_zip_l h₂,
  have h₅ : b₁ ∈ repeat row ( |b + -a| ), from pair_in_zip_r h₂,
  rw ← h₃,
  split; split,
    {exact (range_pure_bounded h₄).1},
    {exact (range_pure_bounded h₄).2},
    {simp [repeat_bounded h₅, uncurry]},
    {rw (repeat_bounded h₅), exact lt_add_succ _ _}
end

lemma length_grp {a b : ℤ} (h : a < b) {x : ℤ} :
  length (grp a b x) = |b - a| :=
have h₁ : length (range_pure a b) = |b - a|,
  from range_length_pure (int.le_of_lt h),
  by simp [grp, length_map, length_zip_left, length_repeat, h₁]

lemma injective_grp {a b} (h : a < b) : injective (grp a b) :=
begin
  intros a₁ a₂,
  induction eq : grp a b a₁ with hd tl ih generalizing a; intros h₁,
    {rw expand_grp h at eq, cases eq},
    {
      rw expand_grp h at eq h₁,
      injection eq with eq₁ eq₂, injection h₁ with h₂ h₃,
      by_cases alt : a + 1 < b,
        {exact ih alt eq₂ h₃},
        {cc}
    }
end

lemma disjoint_grp_neq_row {a b r₁ r₂} (h₀ : r₁ ≠ r₂) :
  disjoint (grp a b r₁) (grp a b r₂) :=
begin
  by_cases h : a < b,
    {
      induction eq : grp a b r₁ with hd tl ih generalizing a,
        {rw expand_grp h at eq, cases eq},
        {
          cases eq₁ : grp a b r₂ with hd₁ tl₁,
            {rw expand_grp h at eq₁, cases eq₁},
            {
              rw expand_grp h at eq₁, rw expand_grp h at eq,
              injection eq₁ with eq₂ eq₃,
              injection eq with eq₄ eq₅,
              clear eq eq₁,
              simp only [mem_cons_iff, disjoint_cons_left, disjoint_cons_right],
              split,
                {
                  intros contra, cases contra,
                    {cc},
                    {
                      rw ← eq₅ at contra,
                      have : hd₁.y = r₁, from in_grp_second contra,
                      clear contra, subst this, subst eq₄, subst eq₅, subst eq₂,
                      cc
                    }
                },
                {
                  split,
                    {
                      intros contra, rw ← eq₃ at contra,
                      have : hd.y = r₂, from in_grp_second contra,
                      clear contra, subst this, subst eq₄, subst eq₅, subst eq₂,
                      cc 
                    },
                    {
                      rw ← eq₃,
                      by_cases h₁ : a + 1 < b,
                        {
                          exact ih h₁ eq₅
                        },
                        {
                          rw not_lt at h₁,
                          rw [grp_empty_iff'.2 h₁, disjoint_comm],
                          exact disjoint_nil_left _,
                        }
                    }
                }
            }
        }
    },
    {rw not_lt at h, simp [grp_empty_iff'.2 h]}
end

def gip (p₁ p₂ : point) : list point :=
  join (map (grp p₁.x p₂.x) (range_pure p₁.y p₂.y))

lemma gip_no_dup {p₁ p₂} : nodup (gip p₁ p₂) :=
begin
  cases p₁ with p₁x p₁y,
  cases p₂ with p₂x p₂y,
  simp only [gip, nodup_join],
  split,
    {
      intros l hl, 
      by_cases h : p₁x < p₂x,
        {
          have : nodup (map (grp p₁x p₂x) (range_pure p₁y p₂y)),
            from nodup_map (injective_grp h) (nodup_range_pure),
          induction l with hd tl ih generalizing p₁x,
            {exact nodup_nil},
            {
              simp only [map, mem_map] at hl,
              rcases hl with ⟨l, ⟨c₁, c₂⟩⟩, rw ← c₂,
              exact nodup_grp
            }
        },
        {
          rw not_lt at h, simp only [map, mem_map] at hl,
          rcases hl with ⟨l', ⟨c₁, c₂⟩⟩,
          rw grp_empty_iff'.2 h at c₂,
          simp [c₂.symm, nodup_nil]
        }
    },
    {
      induction eq : range_pure p₁y p₂y with hd tl ih generalizing p₁y,
        {simp, constructor},
        {
          by_cases h : p₁y < p₂y,
            {
              rw range_pure_next h at eq, injection eq with eq₁ eq₂,
              specialize @ih (p₁y + 1) eq₂,
              simp only [
                and_imp, disjoint_comm, pairwise_cons, map, mem_map, exists_imp_distrib
              ], split; try { assumption },
              intros l x h₁ h₂, subst h₂,
              have : x ≠ hd,
                {
                  intros contra, subst contra, subst eq₁,
                  rw ← eq₂ at h₁,
                  have : p₁y ∉ range_pure (p₁y + 1) p₂y,
                    from @notin_range_pure_of_lt (p₁y + 1) p₂y p₁y (by linarith),
                  contradiction
                },
              exact disjoint_grp_neq_row this
            },
            {
              rw not_lt at h, rw range_pure_empty_iff.2 h at eq,
              cases eq
            }
        }
    }
end

open relative_grid grid

def gip_g := gip (bl g) (gtr g)

private lemma expand_gip {p₁ p₂} (h : p₁ ↗ p₂) :
  gip p₁ p₂ = ⟨p₁.x, p₁.y⟩ :: grp (p₁.x + 1) p₂.x p₁.y
           ++ gip ⟨p₁.x, p₁.y + 1⟩ p₂ :=
  by simp [
       gip, expand_grp (grid_bounded_iff.1 h).1,
       range_pure_next (grid_bounded_iff.1 h).2
     ]

private lemma expand_row_gip {p₁ p₂} (h : p₁ ↗ p₂) :
  gip p₁ p₂ =
  grp p₁.x p₂.x p₁.y ++ gip ⟨p₁.x, p₁.y + 1⟩ p₂ :=
  by simp [gip, range_pure_next (grid_bounded_iff.1 h).2]

private lemma expand_gip_g :
  (gip_g g) = grp (gbl g).x (gtr g).x (gbl g).y
              ++ gip ⟨(gbl g).x, (gbl g).y + 1⟩ ⟨(gtr g).x, ((gtr g).y)⟩ :=
begin
  generalize h : gip ⟨(gbl g).x, (gbl g).y⟩ ⟨(gtr g).x, ((gtr g).y + 1)⟩ = t,
  simp only [gip_g, gip],
  rw range_pure_next, dsimp,
    {apply congr_arg, simp [h.symm, gip]},
    {exact try_lt_bly}
end

def is_in_grid' (xy : point) :=
  is_bounded (gbl g).y (gtr g).y xy.y ∧
  is_bounded (gbl g).x (gtr g).x xy.x

def is_in_grid (bb : bounding_box) (xy : point) :=
  is_bounded bb.p₁.y bb.p₂.y xy.y ∧ is_bounded bb.p₁.x bb.p₂.x xy.x

attribute [reducible]
instance has_mem_grid : has_mem point α := ⟨flip is_in_grid'⟩

attribute [reducible]
instance has_mem_bb : has_mem point bounding_box := ⟨flip is_in_grid⟩

lemma gip_in_grid {p₁ p₂ : point} {h : p₁ ↗ p₂} :
  ∀{a}, a ∈ gip p₁ p₂ → a ∈ (⟨p₁, p₂, h⟩ : bounding_box) :=
assume a h,
begin
  simp [gip] at h,
  cases a with al ar,
  rcases h with ⟨l, ⟨⟨a₁, ⟨h₂, h₃⟩⟩, h₁⟩⟩,
  have h₄ := range_pure_bounded h₂, rw ← h₃ at h₁,
  have h₅ := grp_bounds h₁,
  split; split,
    {
      simp [bounding_box.p₁],
      rcases h₅ with ⟨⟨h₅l₁, h₅l₂⟩, ⟨h₅r₁, h₅r₂⟩⟩,
      cases h₄, transitivity a₁; assumption
    },
    {exact lt_of_le_of_lt (le_of_lt_add_one h₅.2.2) h₄.2},
    {exact h₅.1.1},
    {exact h₅.1.2}
end

def grid_bounds : bounding_box :=
  ⟨gbl g, gtr g, grid_is_bounding_box⟩

lemma grid_bounds_p₁ : (grid_bounds g).p₁ = gbl g := rfl

lemma grid_bounds_p₂ : (grid_bounds g).p₂ = gtr g := rfl

lemma gip_g_in_grid {g : α} :
  ∀{a}, a ∈ gip_g g → a ∈ (grid_bounds g) :=
  assume a h, gip_in_grid h

def make_bounded_idx {g : α} {p : point} (h : p ∈ (grid_bounds g)) :
  bounded (bl g).x (gtr g).x ×
  bounded (gbl g).y (gtr g).y :=
    (make_bounded h.2, make_bounded h.1)

private def make_bounded_indices (is : list point)
                         (h : ∀p, p ∈ is → p ∈ (grid_bounds g)) :
  list (
    bounded (bl g).x (gtr g).x ×
    bounded (gbl g).y (gtr g).y
  ) := map (λp : {x // x ∈ is},
           (⟨p.1.1, (h p.1 p.2).2⟩,
            ⟨p.1.2, (h p.1 p.2).1⟩)) (attach is)

lemma is_bounded_y_of_grid_bounds {g : α} {p} (h : p ∈ (grid_bounds g)) :
  is_bounded (bl g).y (gtr g).y p.y :=
  by simp [grid_bounds, (∈), flip, is_in_grid] at h; exact h.1

lemma is_bounded_x_of_grid_bounds {g : α} {p} (h : p ∈ (grid_bounds g)) :
  is_bounded (bl g).x (gtr g).x p.x :=
  by simp [grid_bounds, (∈), flip, is_in_grid] at h; exact h.2

instance decidable_is_in_grid' {xy : point}
   : decidable (is_in_grid' g xy) :=
   by simp [is_in_grid']; apply_instance

instance decidable_is_in_grid (bb : bounding_box) {xy : point}
   : decidable (is_in_grid bb xy) :=
   by simp [is_in_grid]; apply_instance

instance decidable_is_in_grid'_op {xy : point}
   : decidable (xy ∈ g) :=
   by simp [(∈), is_in_grid', flip]; apply_instance

instance decidable_is_in_grid_op (bb : bounding_box) {xy : point}
   : decidable (xy ∈ bb) :=
   by simp [is_in_grid, (∈), flip]; apply_instance

def inject_into_bounded (p : {x // x ∈ gip_g g}) :
  bounded (bl g).x (gtr g).x ×
  bounded (gbl g).y (gtr g).y :=
  make_bounded_idx (gip_g_in_grid p.2)

private def inject_row_into_bounded
  {a b r} (p : {x // x ∈ grp a b r}) :
  bounded a b × bounded r (r + 1) :=
  ⟨⟨p.1.1, (grp_bounds p.2).1⟩, ⟨p.1.2, (grp_bounds p.2).2⟩⟩

private lemma blgx_trgx_of_mem {g : α} {x} {y} (h : point.mk x y ∈ g) :
  (bl g).x < (gtr g).x :=
  by simp only [(∈), flip, is_in_grid'] at h; exact lt_of_le_of_lt h.2.1 h.2.2

theorem in_gip_g_of_in_g {α : Type*} [grid α] {g : α} {p}
  (h : p ∈ g) : p ∈ gip_g g :=
begin  
  cases p with x y,
  simp [-gtr, gip_g, gip],
  have h₂ : y ∈ range_pure (gbl g).y (gtr g).y,
    by simp [(∈), flip, is_in_grid'] at h; exact in_range_iff.2 h.1,
  split, {
    split,
      {use y, exact ⟨h₂, by simp [grp]⟩},
      {
        generalize h₂ : range_pure ((bl g).x) ((gtr g).x) = l₁,
        generalize h₃ : repeat y ( |(gtr g).x - (bl g).x| ) = l₂,
        rw point_in_zip_prod_iff,
        apply point_in_zip_repeat_right _ h₃ _,
          {
            simp [
              h₂.symm, h₃.symm, range_length_pure, length_repeat,
              int.le_of_lt (blgx_trgx_of_mem h)
            ]
          },
          {
            rw [← h₂, in_range_iff],
            simp only [(∈), flip, is_in_grid'] at h,
            exact h.2
          }
      }
    }
end

theorem in_grid_iff_in_gip_g {p} {g : α} : p ∈ g ↔ p ∈ gip_g g :=
  ⟨
    in_gip_g_of_in_g,
    λh, by apply gip_in_grid h; exact grid_is_bounding_box
  ⟩
 
lemma in_grid_iff_in_grid_bounds {p} {g : α} : p ∈ grid_bounds g ↔ p ∈ g :=
  by split; intros h;
       simp [(∈), flip, is_in_grid, grid_bounds, is_in_grid'] at *;
         exact h

lemma is_bounded_rows_of_in_gip_g {p} {g : α} (h : p ∈ gip_g g) :
  is_bounded (gbl g).y ((gbl g).y + ↑(rows g)) p.y :=
  (in_grid_iff_in_gip_g.2 h).1

lemma is_bounded_cols_of_in_gip_g {p} {g : α} (h : p ∈ gip_g g) :
  is_bounded (gbl g).x ((gbl g).x + ↑(cols g)) p.x :=
  (in_grid_iff_in_gip_g.2 h).2

def grid_point_of_mem {p} (h : p ∈ g) : grid_point g :=
  ⟨make_bounded h.1, make_bounded h.2⟩

def generate :=
  map (abs_data g ∘ grid_point_of_prod ∘ inject_into_bounded g)
      (attach $ gip_g g)

notation `℘` g:max := generate g

section grid_instances

instance vec_grid_functor : functor vec_grid := {
  map := λα β f g, {g with data := vector.map f g.data}
}

instance vec_grid_functor_law : is_lawful_functor vec_grid := {
  id_map := λα ⟨r, c, h, d⟩, by unfold functor.map; simp,
  comp_map := λα β γ f h ⟨r, c, h, d⟩, by simp [(<$>)]
}

instance vec_grid₀_functor : functor vec_grid₀ := {
  map := λα β f g, {g with data := vector.map f g.data}
}

instance vec_grid₀_functor_law : is_lawful_functor vec_grid₀ := {
  id_map := λα ⟨⟨r, c, h, d⟩, o⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨⟨r, c, h, d⟩, o⟩, by simp [(<$>)]
}

instance fgrid₀_functor : functor fgrid₀ := {
  map := λα β f g, {g with data := λx y, f (g.data x y)}
}

instance fgrid₀_functor_law : is_lawful_functor fgrid₀ := {
  id_map := λα ⟨r, c, h, d, o⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨r, c, h, d, o⟩, by simp [(<$>)]
}

end grid_instances

attribute [simp]
lemma vec_grid_fmap_r {α β : Type} {g : vec_grid α} {f : α → β} : (f <$> g).r = g.r :=
  by simp [(<$>)]

attribute [simp]
lemma vec_grid_fmap_c {α β : Type} {g : vec_grid α} {f : α → β} : (f <$> g).c = g.c :=
  by simp [(<$>)]

attribute [simp]
lemma vec_grid₀_fmap_r {α β : Type} {g : vec_grid₀ α} {f : α → β} : (f <$> g).r = g.r
  := by simp [(<$>)]

attribute [simp]
lemma vec_grid₀_fmap_c {α β : Type} {g : vec_grid₀ α} {f : α → β} : (f <$> g).c = g.c
  := by simp [(<$>)]

attribute [simp]
lemma fgrid₀_fmap_r {α β : Type} {g : fgrid₀ α} {f : α → β} : (f <$> g).r = g.r
  := by simp [(<$>)]

attribute [simp]
lemma fgrid₀_fmap_c {α β : Type} {g : fgrid₀ α} {f : α → β} : (f <$> g).c = g.c
  := by simp [(<$>)]

def point_of_bounded_prod {a b c d : ℤ} : bounded a b × bounded c d → point
  | ⟨⟨a, _⟩, ⟨c, _⟩⟩ := ⟨a, c⟩

lemma gip_g_nonempty : ¬empty_list (gip_g g) :=
assume contra,
begin
  simp [gip_g, gip] at contra,
  have c₁ : ¬empty_list (
    range_pure (bl g).y (gtr g).y
  ),
    {
      simp only [empty_list], intros c₂, symmetry' at c₂,
      rw range_pure_empty_iff at c₂,
      have c₃ := @grid_is_bounding_box _ _ g, rw grid_bounded_iff at c₃,
      exact absurd (lt_of_le_of_lt c₂ c₃.2) (lt_irrefl _)
    },
  have c₂ := @not_map_empty_of_not_empty _ _ _
    (grp (bl g).x (tr (bl g) (rows g) (cols g)).x) c₁,
  have c₃ := not_join_empty_of_not_empty contra,
  cases c₃,
    {contradiction},
    {
      revert c₃ contra c₂ c₁,
      generalize c₆ : bl g = bl,
      generalize c₅ : tr bl (rows g) (cols g) = tr',
      generalize c₄ :
        map (grp bl.x tr'.x) (range_pure bl.y (gtr g).y) = l,
      let h₃ := @grid_is_bounding_box _ _ g, rw grid_bounded_iff at h₃,
      simp [gtr, c₆, c₅] at h₃,
      intros,
      have c₅ : ∃z ∈ l, ¬empty_list z,
        {
          let h := grp bl.x tr'.x bl.y,
          have h₁ : h = grp bl.x tr'.x bl.y, by cc,
          use h, split,
            {
              rw h₁, revert c₄,
              generalize h₂ : range_pure bl.y tr'.y = l₁, intros,
              cases l₁ with w ws,
                {
                  rw range_pure_empty_iff at h₂,
                  exact absurd (lt_of_le_of_lt h₂ h₃.2) (lt_irrefl _)
                },
                {
                  have h₄ : w = bl.y,
                    by unfold1 range_pure at h₂; rw if_pos h₃.2 at h₂;
                       injection h₂ with h₃ _; rw h₃,
                  have : bl.y < (gtr g).y, by subst c₅; simp [gtr, c₆]; exact h₃.2,
                  simp [c₄.symm, range_pure_next this]
                },
            },
            {
              unfold1 grp at h₁,
              have h₂ : tr'.x > bl.x, from h₃.1,
              have h₄ : range_pure (bl.x) (tr'.x) =
                        bl.x :: range_pure (bl.x + 1) (tr'.x),
                from range_pure_next h₂,
              rw h₄ at h₁,
              have : |tr'.x - bl.x| ≥ 1,
                begin
                  apply nat.succ_le_of_lt (lt_of_coe_nat_lt_coe_nat _),
                  rw [nat_abs_of_nonneg, lt_sub],
                  simpa, linarith
                end,
              have h₅ : repeat bl.y ( |tr'.x - bl.x| ) =
                bl.y :: repeat bl.y (( |tr'.x - bl.x| ) - 1),
                from repeat_more this,
              rw [h₅, zip_cons_cons, map_cons] at h₁, rw h₁,
              apply not_empty_cons
            }
        },
      rcases c₅ with ⟨c₅l, ⟨c₅₁, c₅₂⟩⟩, rw [← c₄, ← c₅] at c₅₁,
      simp only [gtr] at c₃, subst c₆,
      exact absurd (c₃ c₅l c₅₁) c₅₂
    }
end

lemma length_gip {p₁ p₂ : point} (h : p₁ ↗ p₂) :
  length (gip p₁ p₂) = |p₂.y - p₁.y| * |p₂.x - p₁.x| :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, ← nat_abs_mul],
  rw grid_bounded_iff at h,
  have h₁ : (p₂.y - p₁.y) * (p₂.x - p₁.x) > 0,
    {cases p₁, cases p₂, apply mul_pos; omega},
  simp [
    -sub_eq_add_neg, gip, length_join, (∘), length_grp h.1,
    range_length_pure (int.le_of_lt h.2),
    nat_abs_of_nonneg (int.le_of_lt h₁)
  ],
  repeat {rw nat_abs_of_nonneg}; simp [-sub_eq_add_neg, ge_from_le];
  apply int.le_of_lt; simp [h.1, h.2]
end

theorem length_gip_g : length (gip_g g) = rows g * cols g :=
  by simp [
       gip_g, length_gip, rows_eq_try_sub_bly, cols_eq_trx_sub_blx,
       grid_is_bounding_box
     ]

private theorem length_generate {α : Type*} [grid α] (g : α) :
  length (℘ g) = grid_rows g * grid_cols g :=
by unfold generate gip_g;
   rw [
     length_map, grid_rows_eq_try_sub_bly, grid_cols_eq_trx_sub_blx,
     length_attach, length_gip_g, rows_eq_try_sub_bly, cols_eq_trx_sub_blx
   ]

lemma length_generate_eq_size :
  length (℘ g) = size g := by simp [size, length_generate]

lemma map_generate_map_v₀ {α β : Type} {g : vec_grid₀ α} {f : α → β} :
  f <$> (℘ g) = ℘ (f <$> g) :=
  by simpa [(<$>), generate, abs_data, data, vector.nth_map, (∘)]

lemma map_generate_map_f₀ {α β : Type} (g : fgrid₀ α) {f : α → β} :
  f <$> (℘ g) = ℘ (f <$> g) :=
  by simpa [(<$>), generate, abs_data, data]

lemma dec_grid_len_eq_indices_len :
  length (℘ g) = length (gip_g g) :=
  by simp [length_generate, length_gip_g]

def vec_grid₀_of_fgrid₀ {α : Type} (g : fgrid₀ α) : vec_grid₀ α :=
  {g with data := ⟨℘ g, length_generate_eq_size _⟩}

def fgrid₀_of_vec_grid₀ {α : Type} (g : vec_grid₀ α) : fgrid₀ α :=
  {g with data := λx y, abs_data g ⟨x, y⟩}

instance f₀_v₀_coe {α : Type} : has_coe (fgrid₀ α) (vec_grid₀ α) := ⟨vec_grid₀_of_fgrid₀⟩
instance v₀_f₀_coe {α : Type} : has_coe (vec_grid₀ α) (fgrid₀ α) := ⟨fgrid₀_of_vec_grid₀⟩

attribute [simp]
lemma vec_grid₀_of_fgrid₀_r {α : Type} {g : fgrid₀ α} :
  (vec_grid₀_of_fgrid₀ g).r = g.r := by simp [vec_grid₀_of_fgrid₀]

attribute [simp]
lemma vec_grid₀_of_fgrid₀_c {α : Type} {g : fgrid₀ α} :
  (vec_grid₀_of_fgrid₀ g).c = g.c := by simp [vec_grid₀_of_fgrid₀]

attribute [simp]
lemma vec_grid₀_of_fgrid₀_o {α : Type} {g : fgrid₀ α} :
  (vec_grid₀_of_fgrid₀ g).o = g.o := by simp [vec_grid₀_of_fgrid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_r {α : Type} {g : vec_grid₀ α} :
  (fgrid₀_of_vec_grid₀ g).r = g.r := by simp [fgrid₀_of_vec_grid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_c {α : Type} {g : vec_grid₀ α} :
  (fgrid₀_of_vec_grid₀ g).c = g.c := by simp [fgrid₀_of_vec_grid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_o {α : Type} {g : vec_grid₀ α} :
  (fgrid₀_of_vec_grid₀ g).o = g.o := by simp [fgrid₀_of_vec_grid₀]

attribute [simp]
lemma vec_grid₀_of_fgrid₀_gtr {α : Type} {g : fgrid₀ α} :
  gtr (vec_grid₀_of_fgrid₀ g) = gtr g :=
    by simp [expand_gtr, bl, cols, rows, vec_grid₀_of_fgrid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_gtr {α : Type} {g : vec_grid₀ α} :
  gtr (fgrid₀_of_vec_grid₀ g) = gtr g :=
    by simp [expand_gtr, bl, cols, rows, fgrid₀_of_vec_grid₀]

private theorem nth_le_grp {n} {a b r : ℤ} (h : a < b) (H) :
  nth_le (grp a b r) n H = ⟨a + n, r⟩ :=
begin
  rw ← option.some_inj, rw ← nth_le_nth H,
  induction n with n ih generalizing a b,
    {simp [expand_grp h]},
    {
      simp [expand_grp h],
      have : a + 1 < b,
        begin
          have : a + 1 ≠ b, assume contra, by
            simp [contra.symm, @length_grp a (a + 1) (by cc)] at H;
            clear contra h ih; omega,
          by_contradiction h₁,
          replace h₁ := le_of_not_lt h₁,
          rw le_iff_eq_or_lt at h₁, cases h₁; try { cc },
          have : a = b, by linarith, rw [this, length_grp] at H,
          simp at H, cases H, linarith
        end,
      have lenok : n < length (grp (a + 1) b r),
        begin
          rw length_grp this, rw length_grp h at H,
          have eq₁ : b - (a + 1) ≥ 0, by linarith,
          have eq₂ : b - a ≥ 0, by linarith,
          rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg eq₁],
          rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg eq₂] at H,
          simp, simp at H, linarith
        end,
      specialize @ih (a + 1) b this lenok,
      simp [ih]
    }
end

lemma bl_g_in_g {α : Type*} [grid α] {g : α} : bl g ∈ g :=
begin
  simp only [has_mem.mem, flip, is_in_grid, is_in_grid', is_bounded, gbl],
  split; split; try { linarith },
  exact blgy_lt_trgy,
  exact gblx_lt_gtrx
end

lemma bl_g_in_gip_g {α : Type*} [grid α] {g : α} : bl g ∈ gip_g g :=
  in_grid_iff_in_gip_g.1 bl_g_in_g

theorem nth_grp {n} {a b r : ℤ} (h : a < b) (H : n < length (grp a b r)) :
  nth (grp a b r) n = some ⟨a + n, r⟩ :=
  by rw nth_le_nth H; exact congr_arg _ (nth_le_grp h _)

theorem nth_le_gip {n} {p₁ p₂ : point} (h : p₁ ↗ p₂) (H) :
  nth_le (gip p₁ p₂) n H =
  ⟨p₁.x + n % |p₂.x - p₁.x|, p₁.y + n / |p₂.x - p₁.x|⟩ :=
begin
  cases p₁ with x₁ y₁, cases p₂ with x₂ y₂,
  have x₁x₂ : x₁ < x₂, from (grid_bounded_iff.1 h).1,
  have y₁y₂ : y₁ < y₂, from (grid_bounded_iff.1 h).2,
  rw [← option.some_inj, ← nth_le_nth H], rw length_gip h at H,
  repeat { rw nat_abs_of_nonneg (nonneg_of_lt x₁x₂) },
  simp [-sub_eq_add_neg] at *,
  have : y₂ = y₁ + (y₂ - y₁), by linarith,
  rw this, clear this,
  have : y₂ - y₁ = ↑|y₂ - y₁|,
    by rw nat_abs_of_nonneg; exact nonneg_of_lt y₁y₂,
  rw this, clear this,
  generalize hrows : |y₂ - y₁| = rows, rw hrows at H,
  induction rows with rows ih generalizing y₁ y₂ n,
    {exfalso, simp at H, cases H},
    {
      rw expand_row_gip _,
        {
          by_cases h₁ : n < |x₂ - x₁|,
            {
              simp [-sub_eq_add_neg], rw [nth_split, nth_grp];
              try {simpa [length_grp x₁x₂]},
              congr' 2;
              rw [
                ← int.coe_nat_lt_coe_nat_iff,
                nat_abs_of_nonneg (nonneg_of_lt x₁x₂)
              ] at h₁,
              rw mod_eq_of_lt (coe_zero_le _) h₁,
              rw div_eq_zero_of_lt (coe_zero_le _) h₁,
              simp
            },
            {
              generalize hcols : x₂ - x₁ = cols,
              have rowsnezero : rows ≠ 0, assume contra,
                by simp [contra, -sub_eq_add_neg] at H; contradiction,
              have colsnezero : cols ≠ 0, by linarith,
              have x₂x₁n : |x₂ - x₁| ≤ n, from not_lt.1 h₁,
              have lenok : ¬n < length (grp x₁ x₂ y₁),
                by simpa [length_grp x₁x₂, -sub_eq_add_neg],
              simp [-sub_eq_add_neg], rw nth_split_second lenok,
              by_cases h₂ : y₁ + 1 < y₂,
                {
                  have h₃ : {x := x₁, y := y₁ + 1}↗{x := x₂, y := y₂},
                    from ⟨x₁x₂, h₂⟩,
                  have lenok :
                    n - length (grp x₁ x₂ y₁) < rows * |x₂ - x₁|,
                    {
                      rw nat.succ_mul at H,
                      rw [
                        length_grp x₁x₂, ← int.coe_nat_lt_coe_nat_iff,
                        int.coe_nat_sub x₂x₁n, int.coe_nat_mul,
                        sub_lt_iff_lt_add, ← int.coe_nat_mul, ← int.coe_nat_add
                      ],
                      rwa int.coe_nat_lt_coe_nat_iff
                    },
                  have rowsok : |y₂ - (y₁ + 1)| = rows,
                    by rw [← abs_minus_plus y₁y₂, hrows, nat.succ_sub_one],
                  rw [
                    ← add_assoc,
                    @ih (y₁ + 1) y₂ (n - length (grp x₁ x₂ y₁)) h₃ h₂ rowsok lenok,
                    length_grp x₁x₂
                  ],
                  simp [-sub_eq_add_neg],
                  exact ⟨
                    begin
                      rw [
                        int.coe_nat_sub x₂x₁n, nat_abs_of_nonneg, ← hcols,
                        mod_eq_mod_iff_mod_sub_eq_zero, mod_eq_zero_of_dvd
                      ],
                      simp, rw ← dvd_neg, simp,
                      exact nonneg_of_lt x₁x₂
                    end,
                    begin
                      rw [
                        int.coe_nat_sub x₂x₁n,
                        nat_abs_of_nonneg (nonneg_of_lt x₁x₂), hcols
                      ],
                      simp,
                      have : -cols = cols * (-1 : ℤ), by simp, rw this,
                      rw int.add_mul_div_left _ _ colsnezero,
                      simp
                    end
                  ⟩
                },
                {
                  have h₃ : y₁ + 1 = y₂, by linarith,
                  have h₄ : |y₂ - y₁| = 1, by simp [h₃.symm, add_sub_cancel'],
                  rw h₄ at hrows, injection hrows with contra, cc
                }
            }
      },
      {
        exact ⟨
          (grid_bounded_iff.1 h).1,
          begin
            simp [
              sub_lt_iff_lt_add, lt_add_iff_pos_right, -sub_eq_add_neg
            ],
            exact nat.cases_on rows
              zero_lt_one
              (λ_, lt_trans zero_lt_one (lt_add_succ _ _)),
          end
        ⟩
      }
    }
end

theorem nth_le_gip_g {n} (H) :
  nth_le (gip_g g) n H = ⟨(bl g).x + n % cols g, (bl g).y + n / cols g⟩ :=
begin
  rw cols_eq_trx_sub_blx,
  exact @nth_le_gip n (gbl g) (gtr g) grid_is_bounding_box H
end

theorem nth_gip {n} {p₁ p₂ : point} (h : p₁ ↗ p₂) (H : n < length (gip p₁ p₂)) :
  nth (gip p₁ p₂) n =
  some ⟨p₁.x + n % |p₂.x - p₁.x|, p₁.y + n / |p₂.x - p₁.x|⟩ :=
  by simp [nth_le_nth H, nth_le_gip h]

theorem nth_gip_g {n} (H : n < length (gip_g g)) :
  nth (gip_g g) n = some ⟨(bl g).x + n % cols g, (bl g).y + n / cols g⟩ :=
  by simp [nth_le_nth H, nth_le_gip_g]

theorem nth_generate {n} (H) :
  nth_le (℘ g) n H =
  abs_data g ⟨
    ⟨(bl g).y + n / cols g, ⟨
      by simp,
      idx_div_cols_bounded (by rwa length_generate_eq_size at H)
    ⟩⟩,
    ⟨(bl g).x + n % cols g, ⟨
      by simp,
      idx_mod_cols_bounded⟩
  ⟩⟩ :=
begin
  rw length_generate at H,
  rw [← option.some_inj, ← nth_le_nth],
  simp only [
    abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, expand_gtr,
    generate, nth_map
  ],
  have : n < length (attach (gip_g g)), by simpa [length_attach, length_gip_g],
  simp [
    nth_le_nth this, inject_into_bounded, make_bounded_idx, make_bounded,
    nth_le_gip_g, grid_point_of_prod, data_option
  ]
end

lemma gip_g_expand : gip_g g =
  bl g :: grp ((bl g).x + 1) (gtr g).x (bl g).y ++
  gip ⟨(bl g).x, (bl g).y + 1⟩ (gtr g) :=
begin
  unfold gip_g gip, rw range_pure_next, simp,
  rw expand_grp, simp,
  cases (bl g), simp,
  exact gblx_lt_gtrx,
  exact blgy_lt_trgy
end

theorem nth_generate' {n} (h : n < length ℘ g) :
  nth (℘ g) n =
  some (abs_data g ⟨
    ⟨(bl g).y + n / cols g, ⟨
      by simp,
      idx_div_cols_bounded (by rwa length_generate_eq_size at h)
    ⟩⟩,
    ⟨(bl g).x + n % cols g, ⟨
      by simp,
      idx_mod_cols_bounded⟩
  ⟩⟩) := by simp [nth_le_nth h, congr_arg, nth_generate]

lemma abs_data_eq_nth_v₀ {α : Type} {g : vec_grid₀ α} {p} :
  abs_data g p = vector.nth g.data (grid_point_to_fin p) :=
  by simpa [
       abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, data,
       grid_point_to_fin, rel_point_to_fin
     ]

lemma abs_data_eq_nth_v₀' {α : Type} {g : vec_grid₀ α} {p} :
  abs_data g p =
  vector.nth g.data ⟨|p.y.1 - g.o.y| * g.c + |p.x.1 - g.o.x|,
  begin
    rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, ⟨y, ⟨yl, yu⟩⟩⟩,
    simp [-sub_eq_add_neg],
    simp [-sub_eq_add_neg, expand_gtr, bl, rows, cols] at *,
    rw add_comm,
    have eq₁ : |y - g.o.x| < g.c,
      {
        have : y - (g.o).x ≥ 0, by linarith,
        rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg this],
        linarith
      },
    have eq₂ : |x - g.o.y| < g.r,
      {
        have : x - g.o.y ≥ 0, by linarith,
        rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg this],
        linarith
      },
    exact linearize_array eq₁ eq₂
  end⟩ :=
  by simp [
       abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, data,
       grid_point_to_fin, rel_point_to_fin, bl, rows, cols
     ]

lemma abs_data_eq_nth_f₀ {α : Type} {g : fgrid₀ α} {p} :
  abs_data g p = g.data p.y p.x :=
begin
  rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, ⟨y, ⟨yl, yu⟩⟩⟩,
  simp only [
    abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, data
  ],
  unfold_coes, simp only [fin.val, of_nat_eq_coe],
  have h₁ : x - (bl g).y ≥ 0, by linarith,
  have h₂ : y - (bl g).x ≥ 0, by linarith,
  congr; rw int.nat_abs_of_nonneg; try { assumption };
  simp only [bl];
  linarith
end

lemma some_nth_le_generate_v₀ {α : Type} {g : vec_grid₀ α} {n} (H) :
  some (nth_le (℘ g) n H) =
  nth g.data.to_list ( |↑n % ↑g.c| + |↑n / ↑g.c| * g.c ) :=
begin
  rcases g with ⟨⟨r, c, h, ⟨d, hd⟩⟩, o⟩,
  rw [nth_le_nth, nth_generate],
  simp [abs_data_eq_nth_v₀', expand_gtr, bl, rows, cols, vector.nth, hd],
  rw mod_add_div_coe,
  simp [length_generate, rows, cols] at H,
  simp [H], simpa [hd]
end

lemma nth_generate_v₀ {α : Type} {g : vec_grid₀ α} {n} (H : n < length ℘ g):
  nth (℘ g) n =
  nth g.data.to_list ( |↑n % ↑g.c| + |↑n / ↑g.c| * g.c) :=
  by simp [nth_le_nth, some_nth_le_generate_v₀, H]

private lemma goy_add_n_div_c_lt_goy_add_r {α : Type} {g : fgrid₀ α} {n : ℕ}
  (h : n < length ℘ g) : g.o.y + ↑n / ↑g.c < g.o.y + ↑g.r :=
  begin
    simp [-sub_eq_add_neg], norm_cast,
    rw [length_generate, nat.mul_comm] at h,
    exact nat.div_lt_of_lt_mul h
  end

lemma some_nth_le_generate_f₀ {α : Type} {g : fgrid₀ α} {n} (H) :
  some (nth_le (℘ g) n H) =
  g.data
    ⟨g.o.y + ↑n / ↑g.c, ⟨by simp, goy_add_n_div_c_lt_goy_add_r H⟩⟩
    ⟨g.o.x + ↑n % ↑g.c, ⟨by simp, by simp; exact mod_lt_of_pos _ coe_cols_pos_f⟩⟩
  := by simpa [nth_generate, abs_data_eq_nth_f₀, expand_gtr]

lemma nth_generate_f₀ {α : Type} {g : fgrid₀ α} {n} (H : n < length ℘ g) :
  nth (℘ g) n =
  g.data
    ⟨g.o.y + ↑n / ↑g.c, ⟨by simp, goy_add_n_div_c_lt_goy_add_r H⟩⟩
    ⟨g.o.x + ↑n % ↑g.c, ⟨by simp, by simp; exact mod_lt_of_pos _ coe_cols_pos_f⟩⟩
  := by simp [nth_le_nth H, some_nth_le_generate_f₀]

lemma nth_le_generate_f₀ {α : Type} {g : fgrid₀ α} {n} (H) :
  nth_le (℘ g) n H =
  g.data
    ⟨g.o.y + ↑n / ↑g.c, ⟨by simp, goy_add_n_div_c_lt_goy_add_r H⟩⟩
    ⟨g.o.x + ↑n % ↑g.c, ⟨by simp, by simp; exact mod_lt_of_pos _ coe_cols_pos_f⟩⟩
  := by simpa [nth_generate, abs_data_eq_nth_f₀, expand_gtr]

lemma generate_eq_data {α : Type} (g : vec_grid₀ α) :
  ℘ g = g.data.to_list :=
begin
  have h₁ : length (℘ g) = rows g * cols g,
    from length_generate _,
  have h₂ : length (g.data.to_list) = rows g * cols g,
    by simp [rows, cols],
  apply ext_le (eq.trans h₁ h₂.symm) (λi hi₁ hi₂, _),
  rw h₁ at hi₁, rw h₂ at hi₂,
  have : hi₁ = hi₂, from rfl, subst this, dedup,
  rw ← option.some_inj, repeat { rw ← nth_le_nth },
  rename hi₁_1 hi,
  rcases g with ⟨⟨r, c, h, ⟨data, hd⟩⟩, o⟩,
  simp [-sub_eq_add_neg, rows, cols] at *,
  rw [nth_le_nth (by simpa [length_generate_eq_sizes]), some_nth_le_generate_v₀],
  rw nth_le_nth hi₂, simp,
  have : |↑i % ↑c| + |↑i / ↑c| * c = i, from mod_add_div_coe,
  repeat { rw ← nth_le_nth }, simp [this]
end

private theorem generate_inj_v₀_v₀ {α : Type} {g₁ g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = ℘ g₂) : g₁ = g₂ :=
begin
  repeat { rw generate_eq_data at h },
  rcases g₁ with ⟨⟨g₁r, g₁c, g₁h, g₁d⟩, g₁o⟩,
  rcases g₂ with ⟨⟨g₂r, g₂c, g₂h, g₂d⟩, g₂o⟩,
  dsimp at hrows hcols horig h,
  substs hrows hcols horig,
  congr, exact vector.to_list_inj h
end

lemma nth_le_attach_gip_in_gip_g {α : Type*} [grid α] {g : α} {i} {hi} :
  (nth_le (attach (gip_g g)) i hi).val ∈ gip_g g :=
begin
  rw [nth_le_attach, ← in_grid_iff_in_gip_g, nth_le_gip_g],
  simp only [(∈), flip, is_in_grid', is_bounded],
  split; split,
    {
      have : ↑i / ↑(cols g) ≥ 0,
        by norm_cast; linarith,
      simp [le_add_of_nonneg_right this]
    },
    {
      simp [expand_gtr], norm_cast,
      apply nat.div_lt_of_lt_mul,
      simp [length_attach, length_gip_g] at hi,
      rw mul_comm at hi,
      exact hi
    },
    {
      have : ↑i % ↑(cols g) ≥ 0,
        by norm_cast; linarith,
      simp [le_add_of_nonneg_right this]
    },
    {
      simp [expand_gtr],
      exact mod_lt_of_pos _ coe_cols_pos
    }  
end

theorem grid_eq_iff_v₀_v₀ {α : Type} {g₁ g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
  ⟨λh, h ▸ rfl, generate_inj_v₀_v₀ hrows hcols horig⟩

lemma i_bounded {α : Type*} [grid α] {g : α} {p} (h : p ∈ g) :
  is_bounded 0 (size g) ( |p.y - (bl g).y| * cols g + |p.x - (bl g).x| ) :=
begin
  have h₁ : |p.x - (bl g).x| ≥ 0, by simp,
  have h₂ : |p.y - (bl g).y| ≥ 0, by simp,
  unfold is_bounded, split,
    {linarith},
    {
      simp [(∈), flip, is_in_grid'] at h,
      rcases h with ⟨⟨h₃, h₄⟩, ⟨h₅, h₆⟩⟩,
      have eq₁ : |p.x - (bl g).x| < cols g,
        {
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw cols_eq_trx_sub_blx,
          repeat { rw nat_abs_of_nonneg },
          simpa, simp [expand_gtr], linarith
        },
      have eq₂ : |p.y - (bl g).y| < rows g,
        {
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw rows_eq_try_sub_bly,
          repeat { rw nat_abs_of_nonneg },
          simpa, simp [expand_gtr], linarith
        },
      exact linearize_array eq₁ eq₂
    }
end

private theorem generate_inj_f₀_f₀ {α : Type} {g₁ g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = ℘ g₂) : g₁ = g₂ :=
begin
  have hl₁ : length (℘ g₁) = g₁.r * g₁.c,
    from length_generate _,
  have hl₂ : length (℘ g₂) = g₂.r * g₂.c,
    from length_generate _,
  cases g₁ with g₁r g₁c g₁h g₁o g₁d,
  cases g₂ with g₂r g₂c g₂h g₂o g₂d,
  dsimp at hrows hcols horig hl₁ hl₂,
  subst hrows, subst hcols, subst horig,
  congr, ext x y,
  rcases x with ⟨x, ⟨xl, xu⟩⟩, rcases y with ⟨y, ⟨yl, yu⟩⟩,
  have rowsnezero : g₁r ≠ 0, assume contra,
    by simp [contra] at g₁h; exact absurd g₁h (lt_irrefl _),
  have colsnezero : g₁c ≠ 0, assume contra,
    by simp [contra] at g₂h; exact absurd g₂h (lt_irrefl _),
  let i := |x - g₁o.y| * g₁c + |y - g₁o.x|,
  have hi : i = |x - g₁o.y| * g₁c + |y - g₁o.x|, refl,
  have r_nonneg : x - g₁o.y ≥ 0,
    by simp only [ge_from_le, le_sub_iff_add_le, zero_add]; exact xl,
  have c_nonneg : y - g₁o.x ≥ 0,
    by simp only [ge_from_le, le_sub_iff_add_le, zero_add]; exact yl,
  have i_nonneg : 0 ≤ i, by linarith,
  have i_bounded : i < g₁r * g₁c,
    {
      have yb : y - g₁o.x < ↑g₁c, from sub_lt_iff_lt_add'.2 yu,
      have xb : x - g₁o.y < ↑g₁r, from sub_lt_iff_lt_add'.2 xu,
      rw hi,
      apply linearize_array;
        try { rw ← int.coe_nat_lt_coe_nat_iff };
        rw nat_abs_of_nonneg; try { assumption }
    },
  have h₁ : ∀hh,
    list.nth_le (℘ (
      {r := g₁r, c := g₁c, h := g₁h, o := g₁o, data := g₁d} : fgrid₀ α
    )) i hh =
    list.nth_le (℘ (
      {r := g₁r, c := g₁c, h := g₂h, o := g₁o, data := g₂d} : fgrid₀ α
    )) i (hl₂.symm ▸ i_bounded), { rw h, intro, refl },
  specialize h₁ (hl₁.symm ▸ i_bounded),
  simp [-sub_eq_add_neg, nth_le_generate_f₀] at h₁,
  have : g₁o.y + (↑|y - g₁o.x| + ↑|x - g₁o.y| * ↑g₁c) / ↑g₁c = x,
    {
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      rw @int.add_mul_div_right _ _ ↑g₁c (by simp [colsnezero]),
      rw div_eq_zero_of_lt c_nonneg (sub_lt_iff_lt_add'.2 yu),
      simp
    },
  simp only [this] at h₁,
  have : g₁o.x + ↑|y - g₁o.x| % ↑g₁c = y,
    {
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      rw mod_eq_of_lt c_nonneg (sub_lt_iff_lt_add'.2 yu),
      simp
    },
  simp only [this] at h₁,
  exact h₁
end

theorem grid_eq_iff_f₀_f₀ {α : Type} {g₁ g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
  ⟨λh, h ▸ rfl, generate_inj_f₀_f₀ hrows hcols horig⟩

def row (n : fin (rows g)) :
  (fin (cols g)) → carrier α :=
  data g n

def col (n : fin (cols g)) :
  (fin (rows g)) → carrier α :=
  flip (data g) n

def top :=
  row g ⟨
    0,
    and.elim_left (gt_and_gt_of_mul_gt (nonempty g))
  ⟩

def bot :=
  row g ⟨nat.pred (rows g),
         nat.pred_lt (ne_of_gt (gt_and_gt_of_mul_gt (nonempty g)).1)
        ⟩

def left :=
  have h : cols g > 0,
    from (gt_and_gt_of_mul_gt (nonempty g)).2,
  col g ⟨0, h⟩

def right :=
  have h : cols g > 0,
    from (gt_and_gt_of_mul_gt (nonempty g)).2,
  col g ⟨nat.pred (cols g), nat.pred_lt (ne_of_gt h)⟩

def overlaid_by (bb₁ bb₂ : bounding_box) :=
  (bb₂.p₁.x ≤ bb₁.p₁.x ∧ bb₁.p₂.x ≤ bb₂.p₂.x) ∧
  (bb₁.p₂.y ≤ bb₂.p₂.y ∧ bb₂.p₁.y ≤ bb₁.p₁.y)

def in_grid_bounded (p : point)
  (h : is_in_grid' g p) :=
  let ⟨left, right⟩ :=
    h in (make_bounded left, make_bounded right)

instance overlaid_decidable (p₁ p₂ : bounding_box) :
  decidable (overlaid_by p₁ p₂) := by simp [overlaid_by]; apply_instance

lemma overlaid_by_refl (bb : bounding_box) : overlaid_by bb bb :=
  by simp [overlaid_by]; repeat {split}; refl

lemma overlaid_by_trans {bb₁ bb₂ bb₃ : bounding_box}
  (h : overlaid_by bb₁ bb₂) (h₁ : overlaid_by bb₂ bb₃) : overlaid_by bb₁ bb₃ :=
  by simp [overlaid_by] at *; repeat {split}; transitivity; finish

lemma overlaid_by_antisymm {bb₁ bb₂ : bounding_box}
  (h : overlaid_by bb₁ bb₂) (h₁ : overlaid_by bb₂ bb₁) : bb₁ = bb₂ :=
begin
  simp [overlaid_by] at *,
  rcases bb₁ with ⟨⟨_, _⟩, ⟨_, _⟩⟩, rcases bb₂ with ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  safe
end

lemma overlaid_by_size_le {α : Type*} [grid α] {g : α} {bb : bounding_box}
  (h : overlaid_by bb (grid_bounds g)) :
  bb_size bb ≤ size g :=
begin
  unfold bb_size,
  rw [
    size_eq_rows_mul_cols, rows_of_box, cols_of_box,
    rows_eq_try_sub_bly, cols_eq_trx_sub_blx
  ],
  simp [overlaid_by, grid_bounds] at h,
  rcases h with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩,
  rw ← int.coe_nat_le_coe_nat_iff,
  repeat { rw int.coe_nat_mul },
  cases bb with p₁ p₂ hbb, simp [-sub_eq_add_neg] at *,
  rw grid_bounded_iff at hbb, cases hbb with h₅ h₆,
  repeat { rw nat_abs_of_nonneg; try { linarith } },
  apply mul_le_mul; linarith
end

lemma is_in_larger {bb₁ bb₂ : bounding_box} {xy : point}
  (h : xy ∈ bb₁) (h₁ : overlaid_by bb₁ bb₂) : xy ∈ bb₂ :=
  ⟨⟨le_trans h₁.2.2 h.1.1, lt_of_lt_of_le h.1.2 h₁.2.1⟩,
   ⟨le_trans h₁.1.1 h.2.1, lt_of_lt_of_le h.2.2 h₁.1.2⟩⟩

private def bounded_prod_of_point {p : point} {g : α} (h : p ∈ g) :
  bounded (bl g).x (gtr g).x ×
  bounded (bl g).y (gtr g).y := ⟨make_bounded h.2, make_bounded h.1⟩

open bounding_box

def subgrid (bb : bounding_box) (h : overlaid_by bb (grid_bounds g)) :
            fgrid₀ (carrier α) :=
  ⟨rows_of_box bb, cols_of_box bb,
   mul_pos rows_of_box_pos cols_of_box_pos, bb.p₁,
   λx y, abs_data g ⟨⟨x.1,
    begin
      unfold overlaid_by at h, cases x with x hx, simp,
      rw grid_bounds_p₁ at h, rw grid_bounds_p₂ at h,
      exact ⟨
        le_trans h.2.2 hx.1,
        begin
          have : bb.p₁.y + ↑(rows_of_box bb) = bb.p₂.y,
            begin
              have : (bb.p₂).y - (bb.p₁).y ≥ 0,
                by simp [-sub_eq_add_neg, ge_from_le];
                   apply int.le_of_lt (grid_bounded_iff.1 bb.3).2,
              simp [-sub_eq_add_neg, rows_of_box],
              rw nat_abs_of_nonneg this,
              simp
            end, rw this at hx,
          exact lt_of_lt_of_le hx.2 h.2.1
        end
      ⟩
    end⟩, ⟨y.1,
    begin
      unfold overlaid_by at h, cases y with y hy, simp,
      rw grid_bounds_p₁ at h, rw grid_bounds_p₂ at h,
      have : (bb.p₁).x + ↑(cols_of_box bb) = bb.p₂.x,
        by simp [
             -sub_eq_add_neg, bounding_box.p₁, bounding_box.p₂, cols_of_box,
             nat_abs_of_nonneg (nonneg_of_lt (grid_bounded_iff.1 bb.3).1),
             add_sub_cancel'_right
           ], rw this at hy,
      exact ⟨le_trans h.1.1 hy.1, lt_of_lt_of_le hy.2 h.1.2⟩
    end⟩⟩⟩

theorem length_subgrid {bb} {H} : length ℘(subgrid g bb H) = bb_size bb :=
  by simp [length_generate_eq_size, size, bb_size, subgrid, rows, cols]

lemma gen_subgrid_self :
  ℘ (subgrid g (grid_bounds g) (overlaid_by_refl _)) = @generate _ _ g :=
begin
  have lenok : length ℘(subgrid g (grid_bounds g) (overlaid_by_refl _)) = length ℘ g,
    by simp [
      length_subgrid, length_generate, bb_size, grid_bounds,
      subgrid, rows, cols, rows_of_box, cols_of_box,
      rows_eq_try_sub_bly, cols_eq_trx_sub_blx
    ],
  have eq₁ : rows_of_box (grid_bounds g) = rows g,
    by simp [grid_bounds, rows_of_box, rows_eq_try_sub_bly],
  have eq₂ : cols_of_box (grid_bounds g) = cols g,
    by simp [grid_bounds, cols_of_box, cols_eq_trx_sub_blx],
  have eq₃ : (grid_bounds g).p₁ = bl g,
    by simp [grid_bounds],
  unfold subgrid,
  apply list.ext_le lenok, intros,
  unfold subgrid,
  repeat { rw nth_generate },
  simp [abs_data_eq_nth_f₀, bl, eq₃, cols, eq₁, eq₂]
end

lemma overlaid_by_subgrid_grid {α : Type*} [grid α] {g : α} {bb} {H}
  : overlaid_by (grid_bounds (subgrid g bb H)) (grid_bounds g) :=
begin
  unfold overlaid_by at H,
  rcases bb with ⟨p₁, p₂, hbb⟩,
  rw grid_bounded_iff at hbb,
  cases hbb with hbb₁ hbb₂,
  rcases H with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩,
  simp [grid_bounds, overlaid_by, subgrid, expand_gtr] at *,
  split; split; try {
    simp [bl, expand_gtr, rows, cols, rows_of_box, cols_of_box, -sub_eq_add_neg]
  },
    {assumption},
    {
      have : p₂.x - p₁.x ≥ 0, by linarith,
      rw nat_abs_of_nonneg this,
      linarith
    },
    {
      have : p₂.y - p₁.y ≥ 0, by linarith,
      rw nat_abs_of_nonneg this,
      linarith
    },
    {assumption}
end

lemma bl_subgrid_g_bb_eq_bb_p₁ {α : Type*} [grid α] {g : α} {bb} {H} :
  bl (subgrid g bb H) = bb.p₁ := by simp [subgrid, bl]

lemma tr_subgrid_g_bb_eq_bb_p₂ {α : Type*} [grid α] {g : α} {bb} {H} :
  gtr (subgrid g bb H) = bb.p₂ :=
begin
  simp [expand_gtr, subgrid, bl, rows, cols],
  have eq₁ : cols_of_box bb > 0, from cols_of_box_pos,
  have eq₂ : rows_of_box bb > 0, from rows_of_box_pos,
  rcases bb with ⟨⟨p₁x, p₁y⟩, ⟨p₂x, p₂y⟩, h⟩, rw grid_bounded_iff at h,
  simp [-sub_eq_add_neg, rows_of_box, cols_of_box],
  simp [-sub_eq_add_neg, cols_of_box] at eq₁,
  simp [-sub_eq_add_neg, rows_of_box] at eq₂,
  simp at h, cases h with hl hr,
  rw ← int.coe_nat_lt_coe_nat_iff at eq₁ eq₂,
  rw nat_abs_of_nonneg at eq₁ eq₂,
  all_goals { try { linarith } },
  repeat { rw nat_abs_of_nonneg },
  all_goals { try { linarith } },
  split; linarith
end

lemma grid_bounds_subgrid_g {α : Type*} [grid α] {g : α} {bb} {H} :
  grid_bounds (subgrid g bb H) = bb :=
  by simp [grid_bounds, bl_subgrid_g_bb_eq_bb_p₁, tr_subgrid_g_bb_eq_bb_p₂];
     cases bb; refl

lemma size_subgrid {bb} {H} : size (subgrid g bb H) = bb_size bb :=
  by simp only [
       size, bb_size,
       rows_of_box, cols_of_box, rows_eq_try_sub_bly, cols_eq_trx_sub_blx,
       tr_subgrid_g_bb_eq_bb_p₂, bl_subgrid_g_bb_eq_bb_p₁
     ]

lemma overlaid_by_subgrid_bb {α : Type*} [grid α] {g : α} {bb} {H}
  : overlaid_by bb (grid_bounds (subgrid g bb H)) :=
  by rw grid_bounds_subgrid_g; exact overlaid_by_refl bb

lemma p_in_bb_of_grid_bounds_subgrid_bb_iff {α : Type*} [grid α] {g : α} {bb} {H} {p} :
  p ∈ grid_bounds (subgrid g bb H) ↔ p ∈ bb :=
begin
  split; intros h,
    {
      simp [grid_bounds, flip, is_in_grid] at h,
      simp [(∈), flip, is_in_grid],
      rw [bl_subgrid_g_bb_eq_bb_p₁, tr_subgrid_g_bb_eq_bb_p₂] at h,
      exact h
    },
    {
      simp [grid_bounds, flip, is_in_grid],
      simp [(∈), flip, is_in_grid] at h,
      rw [bl_subgrid_g_bb_eq_bb_p₁, tr_subgrid_g_bb_eq_bb_p₂],
      exact h
    }
end

def inject_filter_bounded {bb : bounding_box}
  (e : {x // x ∈ filter (λ (p : point), p ∉ bb) (gip_g g)}) :
  grid_point g :=
  grid_point_of_mem _ $ in_grid_iff_in_gip_g.2 (mem_filter.1 e.2).1

def subgrid' (bb : bounding_box) (h : overlaid_by bb (grid_bounds g)) :
             list (carrier α) :=
  map (abs_data g ∘ inject_filter_bounded _)
      (attach $ filter (λp, p ∉ bb) (gip_g g))

lemma countp_grp_x {p₁x p₂x a b row} :
  countp (λ (p : point), p.x < p₁x ∨ p₂x ≤ p.x) (grp a b row) =
  countp (λ x, x < p₁x ∨ p₂x ≤ x) (range_pure a b) :=
begin
  induction eq : range_pure a b with hd tl ih generalizing a,
    {
      rw range_pure_empty_iff at eq,
      rw grp_empty_iff'.2 eq,
      refl
    },
    {
      have : a < b,
        {
          by_contradiction contra, rw not_lt at contra,
          rw range_pure_empty_iff.2 contra at eq, cases eq
        },
      rw range_pure_next this at eq, injection eq with eq₁ eq₂, subst eq₁,
      specialize @ih (a + 1) eq₂,
      rw expand_grp this, simp [countp],
      by_cases eq₁ : a < p₁x ∨ p₂x ≤ a; simp [eq₁, ih]
    }
end

lemma countp_grp_single_row_l {α : Type} {l : list α}
  {P₁ P₂ : α → Prop} [decidable_pred P₁] [decidable_pred P₂]
  (h : ∀x ∈ l, ¬P₂ x) :
  countp P₁ l = countp (λ x, P₁ x ∨ P₂ x) l :=
begin
  induction l with hd tl ih,
    {simp},
    {
      simp [countp],
      by_cases eq : (P₁ hd); simp [eq],
        {exact ih (λ_ h₀, h _ (mem_cons_of_mem _ h₀))},
        {
          rw if_neg (h _ _),
          exact ih (λ_ h₀, h _ (mem_cons_of_mem _ h₀)),
          exact mem_cons_self _ _
        }
    }
end

lemma countp_grp_single_row_r {α : Type} {l : list α}
  {P₁ P₂ : α → Prop} [decidable_pred P₁] [decidable_pred P₂]
  (h : ∀x ∈ l, ¬P₂ x) :
  countp P₁ l = countp (λ x, P₂ x ∨ P₁ x) l :=
begin
  induction l with hd tl ih,
    {simp},
    {
      simp [countp],
      by_cases eq : (P₁ hd); simp [eq],
        {exact ih (λ_ h₀, h _ (mem_cons_of_mem _ h₀))},
        {
          rw if_neg (h _ _),
          exact ih (λ_ h₀, h _ (mem_cons_of_mem _ h₀)),
          exact mem_cons_self _ _
        }
    }
end

lemma countp_grp_row {p₁x p₁y p₂x p₂y : ℤ} {blx bly trx : ℤ} 
(h₀ : p₁y < p₂y) (hl : bly ≤ p₁y) :
countp (λ (p : point), (p.y < p₁y ∨ p₂y ≤ p.y) ∨ p.x < p₁x ∨ p₂x ≤ p.x) (grp blx trx bly) =
ite (p₁y = bly) (countp (λ (p : point), p.x < p₁x ∨ p₂x ≤ p.x) (grp blx trx bly))
                (length (grp blx trx bly)) :=
begin
  by_cases h₁ : p₁y = bly,
    {
      have : ∀p : point, p ∈ grp blx trx bly → p.y = bly, from λp, in_grp_second,
      rw if_pos h₁,
      rw ← countp_grp_single_row_r,
      intros p h₂, rw not_or_distrib, subst h₁,
      by_cases h : blx < trx,
        {
          rw expand_grp h at this,
          have eq : p.y = p₁y, from in_grp_second h₂, subst eq,
          split; linarith
        },
        {
          rw not_lt at h, rw grp_empty_iff'.2 h at h₂, cases h₂
        }
    },
    {
      rw if_neg h₁,
      have eq : ∀p : point, p ∈ grp blx trx bly → p.y = bly,
        from λp, in_grp_second,
      have eq₁ : bly < p₁y,
        {
          rw le_iff_eq_or_lt at hl, cases hl, subst hl, contradiction,
          exact hl
        },
      induction iheq : grp blx trx bly with hd tl ih generalizing blx,
        {simp},
        {
          have eq₂ : blx < trx,
            {
              by_contradiction contra, rw not_lt at contra,
              rw grp_empty_iff'.2 contra at iheq, cases iheq
            },
          rw expand_grp eq₂ at iheq, injection iheq with i₁ i₂,
          simp [countp], subst i₁, simp only [point.x, point.y] at *,
          by_cases h₃ : (bly < p₁y ∨ p₂y ≤ bly) ∨ blx < p₁x ∨ p₂x ≤ blx; simp [h₃],
            {
              simp [nat.succ_eq_add_one],
              rw expand_grp eq₂ at eq,
              rw @ih (blx + 1) (λ_ hk, eq _ (mem_cons_of_mem _ hk)) i₂
            },
            {
              repeat { rw not_or_distrib at h₃ },
              rcases h₃ with ⟨⟨a₁, a₂⟩, a₃, a₄⟩,
              linarith
            }
        }
    }
end

lemma in_join_grp_range_iff {blx trx bly try} {p : point}
  (h₀ : blx < trx) :
  p ∈ join (map (grp blx trx) (range_pure bly try)) ↔
  is_bounded blx trx p.x ∧ is_bounded bly try p.y :=
begin
  split; intros h,
    {
      simp at h, rcases h with ⟨l, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩,
      rw in_range_pure_iff at h₁, rw [← h₂, in_grp_iff h₀] at h₃,
      cases h₃ with h₃ h₄, rw ← h₄ at h₁,
      exact ⟨h₃, h₁⟩
    },
    {
      cases h with h h₁, simp,
      use (grp blx trx p.y), use p.y,
      split, {exact in_range_pure_iff.2 h₁}, {refl},
      rw in_grp_iff h₀,
      split, {exact h}, {refl}
    }
end

private lemma filter_any_ {l₁ l₂ : list ℤ} {p₁x p₂x} (h : length l₁ = length l₂) :
  length (filter (λ (x : point), x.x < p₁x ∨ p₂x ≤ x.x)
                 (map (uncurry point.mk) (zip l₁ l₂))) =
  length (filter (λ (x : ℤ), x < p₁x ∨ p₂x ≤ x) l₁) :=
begin
  induction l₁ with hd tl ih generalizing l₂,
    {simp},
    {
      cases l₂ with hd₂ tl₂,
        {simp at h, contradiction},
        {
          simp [uncurry] at *, 
          by_cases eq : hd < p₁x ∨ p₂x ≤ hd; simp [eq]; exact ih h
        }
    }
end

lemma countp_grp {p₁x p₂x a b r : ℤ}
  (h : p₁x < p₂x) (h₁ : a ≤ p₁x) (h₂ : p₂x ≤ b):
  countp (λ (x : point), x.x < p₁x ∨ p₂x ≤ x.x) (grp a b r) =
  nat_abs (p₁x - a) + nat_abs (b - p₂x) :=
begin
  unfold grp, rw countp_eq_length_filter, rw filter_any_,
  rw ← countp_eq_length_filter, rw countp_range_pure h h₁ h₂,
  rw range_length_pure, rw length_repeat, linarith
end

lemma map_length_grp_range {a b c d : ℤ} (h : c ≤ d) (h₁ : a < b) :
   length (join (map (grp a b) (range_pure c d))) =
   |d - c| * |b - a| :=
begin
  generalize eq : range_pure c d = l,
  rw le_iff_eq_or_lt at h, cases h with h h,
    {
      subst h,
      rw range_pure_same_empty at eq, subst eq,
      simp
    },
    {
      induction l with hd tl ih generalizing c,
        {
          rw range_pure_empty_iff at eq,
          have : c = d, by linarith,
          simp [this]
        },
        {
          rw range_pure_next h at eq, injection eq with eq eq₁,
          simp only [map, join, length_append], rw length_grp h₁,
          by_cases eq₂ : c + 1 < d,
            {
              rw @ih (c + 1) eq₁ eq₂, rw ← abs_minus_plus h,
              rw ← int.coe_nat_eq_coe_nat_iff,
              rw int.coe_nat_add, repeat { rw int.coe_nat_mul },
              rw int.coe_nat_sub,
              repeat { rw int.nat_abs_of_nonneg }; try { linarith },
              simp only [int.coe_nat_zero, int.coe_nat_succ, zero_add],
              ring,
              rw ← int.coe_nat_le_coe_nat_iff,
              rw int.nat_abs_of_nonneg; try { linarith },
              simp, linarith
            },
            {
              rw not_lt at eq₂,
              have : c + 1 = d, by linarith, subst this,
              rw range_pure_same_empty at eq₁, subst eq₁,
              simp
            }
        }
    }
end

lemma count_outside_join_map {a b c d p₁x p₂x}
  (h : c < d) (h₁ : p₁x < p₂x) (h₂ : a ≤ p₁x) (h₃ : p₂x ≤ b) :
  countp (λ (p : point), p.x < p₁x ∨ p₂x ≤ p.x) (join (map (grp a b) (range_pure c d))) =
  |p₁x - a| * |d - c| + |b - p₂x| * |d - c| :=
begin
  generalize eq : range_pure c d = l,
  induction l with hd tl ih generalizing c,
    {rw range_pure_empty_iff at eq, linarith},
    {
      by_cases eq₁ : c + 1 < d,
        {
          rw range_pure_next h at eq, injection eq with eq eq₂,
          simp [-sub_eq_add_neg], rw countp_grp; try { linarith },
          rw @ih (c + 1) eq₁ eq₂, repeat { rw ← abs_minus_plus h },
          rw ← int.coe_nat_eq_coe_nat_iff,
          repeat { rw int.coe_nat_add },
          repeat { rw int.coe_nat_mul },
          repeat { rw int.coe_nat_sub },
          simp only [int.coe_nat_zero, int.coe_nat_succ, zero_add],
          repeat { rw int.nat_abs_of_nonneg }; try { linarith },
          ring, rw ← int.coe_nat_le_coe_nat_iff,
          rw int.nat_abs_of_nonneg, simp, linarith, linarith
        },
        {
          rw not_lt at eq₁, rw range_pure_next h at eq,
          have : d = c + 1, by linarith, subst this,
          injection eq with eq eq₂, rw range_pure_same_empty at eq₂,
          subst eq₂, simp [-sub_eq_add_neg], rw countp_grp; try { linarith },
          simp
        }
    }
end

lemma subgrid_smaller_ints {blx bly trx try p₁x p₁y p₂x p₂y}
  (h₀ : p₁x < p₂x) (h₁ : p₁y < p₂y) (h₂ : blx ≤ p₁x) (h₃ : p₂x ≤ trx)
  (h₄ : bly ≤ p₁y) (h₅ : p₂y ≤ try) :
  |p₂y - p₁y| * |p₂x - p₁x| ≤ |try - bly| * |trx - blx| :=
begin
  rw ← int.coe_nat_le_coe_nat_iff,
  repeat { rw int.coe_nat_mul },
  repeat { rw int.nat_abs_of_nonneg }; try { linarith },
  apply mul_le_mul; linarith
end

private lemma count_notin_ {p₁x p₁y p₂x p₂y : ℤ} {blx bly : ℤ} {c r : ℕ}
  (cpos : c > 0) (rpos : r > 0)
  (h₃ : blx ≤ p₁x) (h₄ : p₂x ≤ blx + c) (h₅ : bly ≤ p₁y) (h₆ : p₂y ≤ bly + r)
  (h₇ : p₁x < p₂x) (h₈ : p₁y < p₂y)
  :
  countp (λ (p : point), ((p.y < p₁y ∨ p₂y ≤ p.y) ∨ p.x < p₁x ∨ p₂x ≤ p.x))
      (join (map (grp blx (blx + ↑c)) (range_pure (bly) (bly + ↑r)))) =
    r * c - |p₂y - p₁y| * |p₂x - p₁x| :=
begin
  generalize eq₁ : blx + ↑c = trx,
  generalize eq₂ : bly + ↑r = try,
  have eq₃ : ↑c = trx - blx, by linarith,
  have eq₄ : ↑r = try - bly, by linarith,
  rw ← @nat_abs_of_nonneg (trx - blx) at eq₃; try { linarith },
  rw ← @nat_abs_of_nonneg (try - bly) at eq₄; try { linarith },
  simp [-sub_eq_add_neg] at eq₃ eq₄,
  rw [eq₃, eq₄],
  generalize eq : range_pure bly try = l,
  have : ∃l₁ l₂, l = l₁ ++ l₂ ∧
                     l₁ = range_pure bly p₁y ∧
                     l₂ = range_pure p₁y try,
    from @range_pure_app bly try _ (by linarith) eq.symm _ h₅ (by linarith),
  rcases this with ⟨l₁, ⟨l₂, eq₂, eq₃, eq₄⟩⟩,
  have : ∃ (l₃ l₄ : list ℤ),
            l₂ = l₃ ++ l₄ ∧ l₃ = range_pure p₁y p₂y ∧ l₄ = range_pure p₂y try,
    from @range_pure_app p₁y try _ (by linarith) eq₄ _ (int.le_of_lt h₈) (by linarith),
  rcases this with ⟨l₃, ⟨l₄, eq₅, eq₆, eq₇⟩⟩,
  have eq₈ : l = l₁ ++ l₃ ++ l₄, by rw [eq₂, eq₅, append_assoc], rw eq₈,
  simp [-sub_eq_add_neg], rw [eq₃, eq₆, eq₇],
  rw countp_eq_length_filter,
  rw @filter_congr _ _ (λ_, true),
  swap 2,
    {
      intros, split; intros h₃,
        {trivial},
        {
          rw in_join_grp_range_iff at H,
          unfold is_bounded at H,
          rcases H with ⟨_, ⟨_, c⟩⟩,
          left, left, exact c, linarith
        }
    }, rw filter_true,
  rw countp_eq_length_filter,
  rw @filter_congr _ _ (λp : point, p.x < p₁x ∨ p₂x ≤ p.x),
  swap 2,
    {
      intros, split; intros h₃,
      {
        rw in_join_grp_range_iff at H,
        unfold is_bounded at H,
        rcases H with ⟨⟨c₁, c₂⟩, ⟨c₃, c₄⟩⟩,
        cases h₃ with h₃ h₃; cases h₃ with h₃ h₃,
          {linarith},
          {linarith},
          {left, exact h₃},
          {right, exact h₃},
          {linarith}
      },
      {right, exact h₃}
    },
  rw ← countp_eq_length_filter,
  generalize c₁ :
    countp (λ (p : point), p.x < p₁x ∨ p₂x ≤ p.x)
             (join (map (grp blx trx) (range_pure p₁y p₂y))) =
    n₁,
  rw countp_eq_length_filter,
   rw @filter_congr _ _ (λ_, true),
  swap 2,
    {
      intros, split; intros h₃,
        {trivial},
        {
          rw in_join_grp_range_iff at H,
          unfold is_bounded at H,
          rcases H with ⟨_, ⟨c, _⟩⟩,
          left, right, exact c, linarith
        }
    }, rw filter_true, repeat { rw map_length_grp_range }; try { linarith },
  rw ← c₁, rw count_outside_join_map; try { linarith },
  rw ← int.coe_nat_eq_coe_nat_iff,
  repeat { rw int.coe_nat_add },
  repeat { rw int.coe_nat_mul },
  repeat { rw int.coe_nat_sub },
  repeat { rw int.coe_nat_mul },
  repeat { rw int.nat_abs_of_nonneg }; try { linarith },
  ring,
  apply subgrid_smaller_ints; linarith
end

lemma count_notin {α : Type*} [φ : grid α] {g : α} {bb} {H} :
  countp (λ (p : point), ¬is_in_grid bb p) (gip_g g) =
  size g - size (subgrid g bb H) :=
begin
  rcases bb with ⟨⟨p₁x, p₁y⟩, ⟨p₂x, p₂y⟩, p₃⟩,
  simp [grid_bounded_iff] at p₃,
  simp only [overlaid_by, grid_bounds, expand_gtr] at H,
  simp only [size_subgrid],
  simp only [is_in_grid, is_bounded, not_and_distrib, not_le, not_lt],
  simp only [gip_g, bb_size, rows_of_box, cols_of_box, expand_gtr, gip, size],
  rw ← @count_notin_ p₁x p₁y p₂x p₂y (bl g).x (bl g).y (cols g) (rows g) cols_pos rows_pos H.1.1 H.1.2 H.2.2 H.2.1 p₃.1 p₃.2,
  finish
end

lemma length_subgrid' {α : Type*} [grid α] {g : α} {bb} {H} :
  length (subgrid' g bb H) = size g - size (subgrid g bb H) :=
begin
  simp only [
    subgrid', size_eq_rows_mul_cols, map, length, length_attach, length_map, flip
  ],
  rw ← countp_eq_length_filter,
  exact count_notin
end

-- lemma gip_g_subgrid'_eq_gip_g {α : Type*} [grid α] {g : α} {bb} {H} :
--   gip_g (subgrid' g bb H) = gip_g g := by unfold gip_g; congr

-- lemma grid_bounds_subgrid'_grid {α : Type*} [grid α] {g : α} {bb} {H} :
--   grid_bounds (subgrid' g bb H) = grid_bounds g :=
--   by simp [subgrid', grid_bounds, expand_gbl, expand_gtr, bl, cols, rows]

-- lemma bl_g_subgrid'_eq_bl_g_grid {α : Type*} [grid α] {g : α} {bb} {H} :
--   bl (subgrid' g bb H) = bl g :=
--   let bounds := (@grid_bounds_subgrid'_grid _ _ g bb H) in
--   by simp [grid_bounds] at bounds; exact bounds.1

-- lemma tr_g_subgrid'_eq_tr_g_grid {α : Type*} [grid α] {g : α} {bb} {H} :
--   gtr (subgrid' g bb H) = gtr g :=
--   let bounds := (@grid_bounds_subgrid'_grid _ _ g bb H) in
--   by simp [grid_bounds] at bounds; exact bounds.2

-- lemma overlaid_by_subgrid_subgrid' {α : Type*} [grid α] {g : α} {bb} {H} :
--   overlaid_by (grid_bounds (subgrid g bb H)) (grid_bounds (subgrid' g bb H)) :=
--   by simp [grid_bounds_subgrid'_grid, overlaid_by_subgrid_grid]

lemma p_in_g_iff_p_in_grid_bounds_g {α : Type*} [grid α] {g : α} {p} :
  p ∈ g ↔ p ∈ grid_bounds g :=
begin
  split; intros h,
    {
      simp [grid_bounds, flip, is_in_grid],
      simp [(∈), flip, is_in_grid'] at h,
      exact h
    },
    {
      simp [(∈), flip, is_in_grid'],
      simp [grid_bounds, flip, is_in_grid] at h,
      exact h
    }
end

private lemma abs_data_none_of_subgrid_ {p} {bb} {H} (h : p ∈ gip_g (subgrid g bb H)) :
  p ∈ grid_bounds g :=
begin
  have overlaid : overlaid_by (grid_bounds (subgrid g bb H)) (grid_bounds g),
    from overlaid_by_subgrid_grid,
  rw [← in_grid_iff_in_gip_g, ← in_grid_iff_in_grid_bounds] at h,
  exact is_in_larger h overlaid
end

private def modify_vec
  {α : Type} {m} (v : vector α m) (n : ℕ) (x : α) : vector α m :=
  ⟨update_nth v.to_list n x,
   by simp [update_nth_pres_len, *]⟩

def modify_at {α : Type} (p : point) (x : α) (g : vec_grid₀ α) : vec_grid₀ α :=
  if h : p ∈ g
  then let ⟨r, c⟩ :=
         relpoint_of_gpoint $
           @grid_point.mk _ _ g
           ⟨p.y, by simp only [(∈)] at h; exact h.left⟩
           ⟨p.x, by simp only [(∈)] at h; exact h.right⟩ in
    ⟨⟨g.r, g.c, g.h, modify_vec g.data (r * g.c + c) x⟩, g.o⟩
  else g

def modify_many {α : Type} (l : list (point × α)) (g : vec_grid₀ α) : vec_grid₀ α :=
  foldr (uncurry modify_at) g l

def count_grid {α : Type} [grid α] [decidable_eq (carrier α)]
  (g : α) (x : carrier α) := list.count x (℘ g)

lemma gen_aof_eq_gen {α : Type} {g : fgrid₀ α} :
  ℘ (vec_grid₀_of_fgrid₀ g) = @generate _ ag_fgrid₀ g :=
  by simp [vec_grid₀_of_fgrid₀, generate_eq_data]

private theorem generate_inj_a_f {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = @generate (fgrid₀ α) _ g₂) : g₁ = g₂ :=
begin
  have hl₁ : length (℘ g₁) = g₁.r * g₁.c, from length_generate _,
  have hl₂ : length (℘ g₂) = g₂.r * g₂.c, from length_generate _,
  rcases g₁ with ⟨⟨g₁r, g₁c, g₁h, ⟨g₁dv, g₁dh⟩⟩, g₁o⟩,
  cases g₂ with g₂r g₂c g₂h g₂o g₂d,
  dsimp at hrows hcols horig hl₁ hl₂,
  subst hrows, subst hcols, subst horig,
  unfold_coes,
  simp [vec_grid₀_of_fgrid₀, h.symm, generate_eq_data]
end

lemma gen_foa_eq_gen {α : Type} {g : vec_grid₀ α} :
  ℘ (fgrid₀_of_vec_grid₀ g) = @generate (vec_grid₀ α) _ g :=
begin
  have hl₁ : length (℘ g) = rows g * cols g,
    from length_generate _,
  have hl₂ : length (℘ (fgrid₀_of_vec_grid₀ g)) = rows g * cols g,
    from length_generate _,
  simp [fgrid₀_of_vec_grid₀] at *,
  apply list.ext_le (hl₂.trans hl₁.symm) (λi hi₁ hi₂, _),
  simp [
    nth_le_generate_f₀, nth_generate, abs_data_eq_nth_v₀', abs_data_eq_nth_f₀,
    tl, bl, rows, cols, expand_gtr
  ]
end

private theorem generate_inj_f₀_v₀ {α : Type} {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = @generate (fgrid₀ α) _ g₂) : g₁ = g₂ :=
  generate_inj_f₀_f₀ hrows hcols horig h

theorem grid_eq_iff_v₀_f₀
  {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α}
  (h₁ : g₁.r = g₂.r)
  (h₂ : g₁.c = g₂.c)
  (h₃ : g₁.o = g₂.o) :
  g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
  ⟨λh, h ▸ rfl, λh, generate_inj_a_f h₁ h₂ h₃ $ by rwa gen_aof_eq_gen.symm⟩

theorem grid_eq_iff_f₀_v₀
  {α : Type} {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α}
  (h₁ : g₁.r = g₂.r)
  (h₂ : g₁.c = g₂.c)
  (h₃ : g₁.o = g₂.o) :
  g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
    ⟨λh, h ▸ rfl, λh, generate_inj_f₀_v₀ h₁ h₂ h₃ h⟩

@[ext]
theorem grid_eq_ext_v₀_v₀ {α : Type} {g₁ g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_v₀_v₀ hrows hcols horig).2

@[ext]
theorem grid_eq_ext_f₀_f₀ {α : Type} {g₁ g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_f₀_f₀ hrows hcols horig).2

@[ext]
theorem grid_eq_ext_v₀_f₀ {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_v₀_f₀ hrows hcols horig).2

@[ext]
theorem grid_eq_ext_f₀_v₀ {α : Type} {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_f₀_v₀ hrows hcols horig).2

lemma nth_vecgrid_of_fgrid {α : Type} {g : fgrid₀ α} {n} :
  list.nth (vec_grid₀_of_fgrid₀ g).data.val n = list.nth (℘ g) n :=
  by delta vec_grid₀_of_fgrid₀; simp

instance decidable_eq_v₀_v₀ {α : Type} [decidable_eq α]
  : decidable_eq (vec_grid₀ α) :=
  λg₁ g₂, if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
            by simp [grid_eq_iff_v₀_v₀, *]; apply_instance
          else is_false $ by finish

instance decidable_eq_f₀_f₀ {α : Type} [decidable_eq α]
  : decidable_eq (fgrid₀ α) :=
  λg₁ g₂, if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
            by simp [grid_eq_iff_f₀_f₀, *]; apply_instance
          else is_false $ by finish

instance decidable_eq_v₀_f₀ {α : Type} [decidable_eq α]
  {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α} : decidable (g₁ = g₂) :=
  if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
    by simp [grid_eq_iff_v₀_f₀, *]; apply_instance    
  else is_false $ by finish

instance decidable_eq_f₀_v₀ {α : Type} [decidable_eq α]
  {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α} : decidable (g₁ = g₂) :=
  if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
    by simp [grid_eq_iff_f₀_v₀, *]; apply_instance
  else is_false $ by finish

lemma subgrid_self {α : Type} {g : vec_grid₀ α} {bb : bounding_box}
  (h : bb = {bounding_box. p₁ := bl g, p₂ := gtr g, h := grid_is_bounding_box })
  : subgrid g bb begin unfold grid_bounds, rw h, exact overlaid_by_refl _ end =
    g :=
begin
  rcases g with ⟨⟨r, c, h, ⟨d, hd⟩⟩, o⟩,
  simp [h, subgrid], unfold_coes,
  rw grid_eq_iff_f₀_f₀;
    try { simp [cols_of_box, bl, expand_gtr, cols] };
    try { simp };
    try { simp [rows_of_box, bl, expand_gtr, rows] },
  rw gen_foa_eq_gen,
  apply ext_le,
    {
      simp [
        length_generate_eq_size, size, rows, cols,
        rows_of_box, cols_of_box, bl, expand_gtr
      ]
    },
    {
      intros,
      rw nth_le_generate_f₀,
      simp only [
        nth_generate, abs_data, data, expand_gtr, bl, (∘),
        relpoint_of_gpoint, prod_of_rel_point, rows, cols, tl,
        rows_of_box, cols_of_box
      ], simp
    }
end

lemma p_in_g_iff_v₀_f₀ {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α} {p}
                     (h₁ : g₁.r = g₂.r)
                     (h₂ : g₁.c = g₂.c)
                     (h₃ : g₁.o = g₂.o) : p ∈ g₁ ↔ p ∈ g₂ :=
begin
  rcases g₁ with ⟨⟨r₁, c₁, gh₁, d₁⟩, o₁⟩,
  rcases g₂ with ⟨r₂, c₂, gh₂, o₂, d₂⟩,
  simp [flip, is_in_grid'] at *,
  split; intros; unfold_projs at *;  
  subst h₁; subst h₂; subst h₃; finish
end

lemma cols_subgrid {bb} {H} :
  cols (subgrid g bb H) = cols_of_box bb := rfl

lemma rows_subgrid {bb} {H} :
  rows (subgrid g bb H) = rows_of_box bb := rfl

private lemma expand_repeat_app {α : Type} {l₁ l₂ l₃ : list α} {r : ℤ} :
  repeat r (length (l₁ ++ l₂ ++ l₃)) = 
  repeat r (length l₁) ++ repeat r (length l₂) ++ repeat r (length l₃) :=
  by simp [repeat_add]

private lemma expand_map_zip_repeat {l₁ l₂ l₃} {r : ℤ} :
  map (uncurry point.mk) (zip (l₁ ++ l₂ ++ l₃) (repeat r (length (l₁ ++ l₂ ++ l₃)))) =
  map (uncurry point.mk) (zip l₁ (repeat r (length l₁))) ++
  map (uncurry point.mk) (zip l₂ (repeat r (length l₂))) ++
  map (uncurry point.mk) (zip l₃ (repeat r (length l₃))) :=
begin
  repeat { rw ← map_append }, congr,
  rw expand_repeat_app,
  repeat { rw zip_append },
  rw length_repeat,
  simp
end

lemma filter_cols_grp_range_pure {p₁x p₂x gbl gtr r}
  (h : p₁x < p₂x) (h₁ : gbl ≤ p₁x) (h₂ : p₂x ≤ gtr) :
  filter (λ (p : point), p₁x ≤ p.x ∧ p.x < p₂x) (grp gbl gtr r) =
  grp p₁x p₂x r :=
begin
  unfold grp,
  generalize eq : range_pure gbl gtr = l,
  have : ∃l₁ l₂, l = l₁ ++ l₂ ∧
                 l₁ = range_pure gbl p₁x ∧
                 l₂ = range_pure p₁x gtr,
  from @range_pure_app gbl gtr _ (by linarith) eq.symm _ h₁ (by linarith),
  rcases this with ⟨l₁, ⟨l₂, eq₁, eq₂, eq₃⟩⟩,
  have : ∃l₃ l₄, l₂ = l₃ ++ l₄ ∧
                 l₃ = range_pure p₁x p₂x ∧
                 l₄ = range_pure p₂x gtr,
  from @range_pure_app p₁x gtr _ (by linarith) eq₃ _ (int.le_of_lt h) h₂,
  rcases this with ⟨l₃, ⟨l₄, eq₄, eq₅, eq₆⟩⟩,
  rw [eq₁, eq₄], rw ← eq₅, rw ← append_assoc,
  have : length (l₁ ++ l₃ ++ l₄) = |gtr - gbl|,
    {
      have : l = l₁ ++ l₃ ++ l₄,
        by simp [append_assoc, *], rw ← this,
      rw ← eq, apply range_length_pure, linarith
    }, rw ← this,
  rw expand_map_zip_repeat, simp, rw eq₂,
  rw @filter_congr _ _ (λ_, false), swap 2,
    {
      intros, split; intros H₁, cases x with x y,
      have eq₇ :
        x ∈ range_pure gbl p₁x ∧
        y ∈ repeat r (length (range_pure gbl p₁x)),
      from in_zip_of H,
      cases eq₇ with eq₇ eq₈,
      simp at H₁,
      rw in_range_pure_iff at eq₇,
      have : y = r, from eq_of_mem_repeat eq₈,
      subst this,
      unfold is_bounded at eq₇,
      cases H₁, cases eq₇, linarith,
      contradiction
    },
  rw [filter_false, nil_append], rw eq₅,
  rw @filter_congr _ _ (λ_, true), swap 2,
    {
      intros, split; intros H₁,
      trivial,
      cases x with x y,
      have eq₇ :
        x ∈ range_pure p₁x p₂x ∧
        y ∈ repeat r (length (range_pure p₁x p₂x)),
      from in_zip_of H,
      cases eq₇ with eq₇ eq₈,
      rw in_range_pure_iff at eq₇,
      have : y = r, from eq_of_mem_repeat eq₈,
      subst this,
      exact eq₇
    }, rw filter_true, rw eq₆,
  rw @filter_congr _ _ (λ_, false), swap 2,
    {
      intros, split; intros H₁, cases x with x y,
      have eq₇ :
        x ∈ range_pure p₂x gtr ∧
        y ∈ repeat r (length (range_pure p₂x gtr)),
      from in_zip_of H,
      cases eq₇ with eq₇ eq₈,
      simp at H₁,
      rw in_range_pure_iff at eq₇,
      have : y = r, from eq_of_mem_repeat eq₈,
      subst this,
      unfold is_bounded at eq₇,
      cases H₁, cases eq₇, linarith,
      contradiction
    },
  rw [filter_false, append_nil],
  rw range_length_pure,
  simp, linarith
end

private lemma filter_bbox_gip {p₁x p₂x gbl gtr} {l}
  (h : p₁x < p₂x) (h₁ : gbl ≤ p₁x) (h₂ : p₂x ≤ gtr) :
  filter (λ (p : point), p₁x ≤ p.x ∧ p.x < p₂x)
    (join (map (grp gbl gtr) l)) = join (map (grp p₁x p₂x) l) :=
begin
  induction l with hd tl ih,
    {simp},
    {simp, rw ih, rw filter_cols_grp_range_pure; linarith}
end

lemma filter_generate_subgrid {α : Type*} [grid α]
  {g : α} {bb} {H} :
  filter (λ (p : point), p ∈ bb) (gip_g g) =
  gip_g (subgrid g bb H) :=
begin
  rcases bb with ⟨p₁, p₂, hbb⟩, rw grid_bounded_iff at hbb,
  cases hbb with hbb₁ hbb₂,
  unfold gip_g gip,
  rw bl_subgrid_g_bb_eq_bb_p₁,
  rw tr_subgrid_g_bb_eq_bb_p₂, simp at *,
  generalize eq : range_pure p₁.y p₂.y = l,
  generalize eq₁ : range_pure (bl g).y (gtr g).y = l₁,
  unfold overlaid_by at H,
  rcases H with ⟨⟨c₁, c₂⟩, c₃, c₄⟩, simp [grid_bounds] at *,
  have : ∃l₂ l₃, l₁ = l₂ ++ l₃ ∧
                     l₂ = range_pure (bl g).y p₁.y ∧
                     l₃ = range_pure p₁.y (gtr g).y,
  from @range_pure_app (bl g).y (gtr g).y _ blgy_lt_trgy eq₁.symm _ c₄ (by linarith),
  rcases this with ⟨l₂, ⟨l₃, eq₂, eq₃, eq₄⟩⟩,
  have : ∃l₄ l₅, l₃ = l₄ ++ l₅ ∧
                 l₄ = range_pure p₁.y p₂.y ∧
                 l₅ = range_pure p₂.y (gtr g).y,
  from @range_pure_app p₁.y (gtr g).y _ (lt_of_lt_of_le hbb₂ c₃) eq₄ _ (int.le_of_lt hbb₂) (by linarith),
  rcases this with ⟨l₄, ⟨l₅, eq₅, eq₆, eq₇⟩⟩,
  rw eq₂, rw eq₅,
  have eq₈ : l₄ = l, by cc, subst eq₈,
  simp only [flip, is_in_grid, is_bounded],
  simp, rw eq₃, rw eq₆, rw eq₇,
  rw @filter_congr _ _ (λ_, false), swap 2,
  intros, split; intros H₁,
    {
      rw in_join_grp_range_iff at H, unfold is_bounded at H,
      have contra₁ : p₁.y ≤ x.y, from H₁.1.1,
      have contra₂ : x.y < p₁.y, from H.2.2,
      linarith,
      exact gblx_lt_gtrx
    },
    {
      contradiction
    }, rw [filter_false, nil_append],
  generalize protect :
    filter (λ (p : point), (p₁.y ≤ p.y ∧ p.y < p₂.y) ∧ p₁.x ≤ p.x ∧ p.x < p₂.x)
           (join (map (grp ((bl g).x) ((gtr g).x)) (range_pure (p₁.y) (p₂.y)))) = prot₁,
  rw @filter_congr _ _ (λ_, false), swap 2,
  intros, split; intros H₁,
    {
      rw in_join_grp_range_iff at H, unfold is_bounded at H,
      have contra₁ : x.y < p₂.y, from H₁.1.2,
      have contra₂ : p₂.y ≤ x.y, from H.2.1,
      linarith,
      exact gblx_lt_gtrx
    },
    {
      contradiction
    }, rw [filter_false, append_nil],
  rw ← protect,
  rw @filter_congr _ _ (λ (p : point), p₁.x ≤ p.x ∧ p.x < p₂.x),
  swap 2,
    {
      intros, split; intros H₁,
      exact H₁.right,
      rw in_join_grp_range_iff at H, unfold is_bounded at H,
      exact ⟨H.2, H₁⟩,
      exact gblx_lt_gtrx
    },
    {
      rw filter_bbox_gip; linarith
    }
end

lemma nth_le_filter_mem_gip {n} {bb : bounding_box} {H}
  (h : overlaid_by bb (grid_bounds g)) :
  nth_le (filter (λ (p : point), p ∈ bb) (gip_g g)) n H =
    {x := bb.p₁.x + ↑n % ↑(cols_of_box bb),
     y := bb.p₁.y + ↑n / ↑(cols_of_box bb)} :=
begin
  rw ← option.some_inj, rw ← nth_le_nth,
  rw @filter_generate_subgrid _ _ _ _ h, rw nth_gip_g,
  rw bl_subgrid_g_bb_eq_bb_p₁,
  refl, rw @filter_generate_subgrid _ _ _ _ h at H,
  exact H
end

lemma rows_of_overlaid_le {α : Type*} [grid α] {g : α} {bb}
  (H : overlaid_by bb (grid_bounds g)) : rows_of_box bb ≤ rows g :=
begin
  unfold rows_of_box, unfold overlaid_by grid_bounds at H, simp at H,
  rcases H with ⟨⟨h₁, h₂⟩, h₃, h₄⟩,
  rw rows_eq_try_sub_bly,
  rw ← int.coe_nat_le_coe_nat_iff,
  repeat { rw int.nat_abs_of_nonneg },
  linarith,
  rw expand_gtr, simp,
  cases bb, simp at *, rw grid_bounded_iff at bb_h, cases bb_h, linarith
end

lemma cols_of_overlaid_le {α : Type*} [grid α] {g : α} {bb}
  (H : overlaid_by bb (grid_bounds g)) : cols_of_box bb ≤ cols g :=
begin
  unfold cols_of_box, unfold overlaid_by grid_bounds at H, simp at H,
  rcases H with ⟨⟨h₁, h₂⟩, h₃, h₄⟩,
  rw cols_eq_trx_sub_blx,
  rw ← int.coe_nat_le_coe_nat_iff,
  repeat { rw int.nat_abs_of_nonneg },
  linarith,
  rw expand_gtr, simp,
  cases bb, simp at *, rw grid_bounded_iff at bb_h, cases bb_h, linarith
end

lemma size_subgrid_le_grid {α : Type*} [grid α] {g : α} {bb} {H} :
  size (subgrid g bb H) ≤ size g :=
begin
  rw size_subgrid, unfold bb_size size,
  apply mul_le_mul,
  exact rows_of_overlaid_le H,
  exact cols_of_overlaid_le H,
  exact le_of_lt cols_of_box_pos,
  exact le_of_lt rows_pos
end

private lemma filter_congr_heq {α : Type} {l₁ l₂ : list α}
  (h : l₁ = l₂) {P₁ : {x : α | x ∈ l₁} → Prop} {P₂ : {x : α | x ∈ l₂} → Prop}
  [decidable_pred P₁] [decidable_pred P₂]
  (h₁ : ∀x : α, x ∈ l₁ → (P₁ ⟨x, by simp [a]⟩ ↔ P₂ ⟨x, begin simp, rw ← h, exact a end⟩)) :
  length (filter P₁ (attach l₁)) = length (filter P₂ (attach l₂)) :=
begin
  resetI, subst h,
  have : P₁ = P₂,
    {
      apply funext,
      intros, cases x with x hx, simp at hx,
      simp,
      split; intros h,
        {
          specialize h₁ x hx, 
          rw ← h₁,
          exact h
        },
        {
          specialize h₁ x hx, 
          rw h₁,
          exact h
        }
    },
  subst this,
  finish
end

private lemma filter_congr_heq' {α : Type} {l₁ l₂ : list α}
  (h : l₁ = l₂) {P₁ : {x : α // x ∈ l₁} → Prop} {P₂ : {x : α // x ∈ l₂} → Prop}
  [decidable_pred P₁] [decidable_pred P₂]
  (h₁ : ∀x : α, x ∈ l₁ → (P₁ ⟨x, by simp [a]⟩ ↔ P₂ ⟨x, begin rw ← h, exact a end⟩)) :
  length (filter P₁ (pmap subtype.mk l₁ (λ_, id))) = length (filter P₂ (pmap subtype.mk l₂ (λ_, id))) :=
  filter_congr_heq h h₁ 

lemma count_subgrid_in_bb {α : Type*} [grid α] [decidable_eq (carrier α)]
  (g : α) {bb} {H₁} {elem : carrier α} :
  count elem (@generate _ _  (subgrid g bb H₁)) =
  countp
    (λ (x : {x // x ∈ filter (λ (p : point), p ∈ bb) (gip_g g)}),
        elem = abs_data g {
  x := ⟨(x.val).x,
  begin
    rcases x with ⟨⟨x, y⟩, hx⟩, simp, rw mem_filter at hx,
    cases hx with hx₁ hx₂,
    rw ← in_grid_iff_in_gip_g at hx₁,
    exact hx₁.2
  end⟩,
  y := ⟨(x.val).y,
  begin
    rcases x with ⟨⟨x, y⟩, hx⟩, simp, rw mem_filter at hx,
    cases hx with hx₁ hx₂,
    rw ← in_grid_iff_in_gip_g at hx₁,
    exact hx₁.1
  end⟩})
    (attach (filter (λ (p : point), p ∈ bb) (gip_g g))) :=
begin
  simp only [count, generate], repeat { rw countp_eq_length_filter },
  rw filter_of_map, rw length_map,
  simp only [
    (∘), inject_into_bounded, grid_point_of_prod, make_bounded,
    make_bounded_idx
  ],
  let eq := @filter_generate_subgrid _ _ g bb H₁, symmetry' at eq,
  apply filter_congr_heq eq,
  rintros ⟨x, y⟩ p,
  split; intros h; simp [h];  
  rw abs_data_eq_nth_f₀;
  delta subgrid; simp; refl
end

lemma filter_partition_dependent'
  {α : Type} [decidable_eq α] {l : list α}
  {Q : α → Prop} {R : α → Prop}
  [decidable_pred Q] [decidable_pred R]
  {β} {P : β → Prop} [decidable_pred P]
  (h : ∀x, ¬Q x ↔ R x)
  (p : α → Prop) (f : ∀ a, p a → β)
  {β₁} (i₁ : β₁ → β) (p₁ : α → Prop) (f₁ : ∀ a, p₁ a → β₁)
  {β₂} (i₂ : β₂ → β) (p₂ : α → Prop) (f₂ : ∀ a, p₂ a → β₂) :
  ∀ (H : ∀ (a : α), a ∈ l → p a)
    (H₁ : ∀ (a : α), a ∈ filter Q l → p₁ a)
    (H₂ : ∀ (a : α), a ∈ filter R l → p₂ a)
    (heq : ∀x (H₃ : x ∈ l) (H₄ : Q x), P (f x (H x H₃)) → P (i₁ (f₁ x (H₁ x (by simp [H₃, H₄])))))
    (heq₁ : ∀x (H₃ : x ∈ l) (H₄ : R x), P (f x (H x H₃)) → P (i₂ (f₂ x (H₂ x (by simp [H₃, H₄])))))
    (heq₂ : ∀x (H₃ : x ∈ l) (H₄ : Q x), ¬P (f x (H x H₃)) → ¬P (i₁ (f₁ x (H₁ x (by simp [H₃, H₄])))))
    (heq₃ : ∀x (H₃ : x ∈ l) (H₄ : R x), ¬P (f x (H x H₃)) → ¬P (i₂ (f₂ x (H₂ x (by simp [H₃, H₄]))))),
  length (filter P (pmap f l H)) =
  length (filter (λ x, P (i₁ x)) (pmap f₁ (filter Q l) H₁)) +
  length (filter (λ x, P (i₂ x)) (pmap f₂ (filter R l) H₂)) :=
begin
  induction l with hd tl ih; intros,
    {simp},
    {
      by_cases h₁ : P (f hd (H _ (mem_cons_self _ _))),
        {
          unfold pmap,
          rw filter_cons_of_pos _ h₁,
          rw length_cons,
          by_cases h₂ : Q hd,
            {
              simp [filter_cons_of_pos _ h₂, -add_comm],
              have : ¬R hd, by finish,
              simp [filter_cons_of_neg _ this, -add_comm],
              have h₃ : P (i₁ (f₁ hd (H₁ _ (by simp [h₂])))),
                {
                  apply heq, exact h₂, exact h₁
                },
              simp [h₃], rw add_comm,
              apply ih,
              intros, apply heq, exact H₄, exact a, right, exact H₃,
              intros, apply heq₁, exact H₄, exact a, right, exact H₃,
              intros, apply heq₂, exact H₄, exact a, right, exact H₃,
              intros, apply heq₃, exact H₄, exact a, right, exact H₃
            },
            {
              simp [filter_cons_of_neg _ h₂, -add_comm],
              have : R hd, by finish,
              simp [filter_cons_of_pos _ this, -add_comm],
              have h₃ : P (i₂ (f₂ hd (H₂ _ (by simp [this])))),
                {
                  apply heq₁, exact this, exact h₁
                },
              simp [h₃],
              apply ih,
              intros, apply heq, exact H₄, exact a, right, exact H₃,
              intros, apply heq₁, exact H₄, exact a, right, exact H₃,
              intros, apply heq₂, exact H₄, exact a, right, exact H₃,
              intros, apply heq₃, exact H₄, exact a, right, exact H₃
            }
        },
        {
          unfold pmap,
          rw filter_cons_of_neg _ h₁,
          by_cases h₂ : Q hd,
            {
              simp [filter_cons_of_pos _ h₂, -add_comm],
              have : ¬R hd, by finish,
              simp [filter_cons_of_neg _ this, -add_comm],
              have h₃ : ¬P (i₁ (f₁ hd (H₁ _ (by simp [h₂])))),
                {
                  apply heq₂, exact h₂, exact h₁
                },
              simp [h₃], rw add_comm,
              apply ih,
              intros, apply heq, exact H₄, exact a, right, exact H₃,
              intros, apply heq₁, exact H₄, exact a, right, exact H₃,
              intros, apply heq₂, exact H₄, exact a, right, exact H₃,
              intros, apply heq₃, exact H₄, exact a, right, exact H₃
            },
            {
              simp [filter_cons_of_neg _ h₂, -add_comm],
              have : R hd, by finish,
              simp [filter_cons_of_pos _ this, -add_comm],
              have h₃ : ¬P (i₂ (f₂ hd (H₂ _ (by simp [this])))),
                {
                  apply heq₃, exact this, exact h₁
                },
              simp [h₃],
              apply ih,
              intros, apply heq, exact H₄, exact a, right, exact H₃,
              intros, apply heq₁, exact H₄, exact a, right, exact H₃,
              intros, apply heq₂, exact H₄, exact a, right, exact H₃,
              intros, apply heq₃, exact H₄, exact a, right, exact H₃
            }
        }
    }
end

private lemma count_partition_over_filter
  {α : Type} {l : list α} [decidable_eq α]
  {P : α → Prop} [decidable_pred P]
  {P₃ : α → Prop} [decidable_pred P₃]
  {P₅ : {x // x ∈ l} → Prop} [decidable_pred P₅]
  (h : ∀x, ¬P x ↔ P₃ x) :
  length (filter (λ (x : {x // x ∈ l}), P₅ x) (attach l)) =
  length (filter (λ (x : {x // x ∈ filter P l}), P₅ ⟨x.1, in_l_of_in_filter x.2⟩) (attach (filter P l))) +
  length (filter (λ (x : {x // x ∈ filter P₃ l}), P₅ ⟨x.1, in_l_of_in_filter x.2⟩) (attach (filter P₃ l))) :=
begin
  apply filter_partition_dependent', exact h,
  intros, exact a,
  intros, exact a,
  intros, exact a,
  intros, exact a
end

lemma count_split {α : Type*} [grid α] [decidable_eq (carrier α)] (g : α) (bb) (H₁)
  {elem : carrier α} :
  count elem (℘ g) =
  count elem (@generate _ _ (subgrid g bb H₁)) +
  count elem (subgrid' g bb H₁) :=
begin
  rw count_subgrid_in_bb,
  simp only [
    generate, subgrid', comp, grid_point_of_prod,
    inject_into_bounded, make_bounded, make_bounded_idx, gbl, map,
    inject_filter_bounded, grid_point_of_mem 
  ],
  simp only [
    count, countp_eq_length_filter,
    filter_of_map, gbl, map, length, length_map
  ],
  simp only [(∘)],
  apply count_partition_over_filter, finish
end

end finite_grid

section grid_instances

open relative_grid

def split_rows_cols : ℕ → ℕ → list string → list string
  | cols 0 ls := [""]
  | cols (k + 1) ls := list.take cols ls ++ ["\n"]
                       ++ split_rows_cols cols k (list.drop cols ls)

def grid_str {α : Type*} [grid α]
  [has_to_string (carrier α)] (g : α) : string :=
  let points := list.map to_string $ ℘ g in
    " " ++ (list.foldr append "" $
                       list.intersperse " " $
                       split_rows_cols (cols g)
                                       (rows g) points)

instance grid_repr {α : Type*} [grid α]
  [has_to_string (carrier α)] : has_repr α := ⟨grid_str⟩

instance grid_to_string {α : Type*} [grid α]
  [has_to_string (carrier α)] : has_to_string α := ⟨grid_str⟩

-- def test_grid : vec_grid₀ ℕ :=
--   vec_grid₀.mk ⟨4, 5, dec_trivial,
--     ⟨[1, 2, 3, 4, 5,
--       1, 2, 3, 4, 5,
--       1, 2, 3, 4, 5,
--       1, 2, 3, 4, 5], rfl⟩⟩ ⟨0, 0⟩
-- def testbb : bounding_box := ⟨⟨0, 0⟩, ⟨2, 3⟩, sorry⟩
-- #eval list.filter (λx, x ∈ testbb) (gip_g test_grid)
-- #eval gip_g (subgrid test_grid testbb sorry)
-- #eval list.count 4 (℘ test_grid)
-- #eval list.count 4 (℘ (subgrid test_grid testbb sorry))
-- #eval list.count 4 ((subgrid' test_grid testbb sorry))
-- #eval (subgrid' test_grid testbb sorry)
-- -- 16, 17, 18, 19, 20
-- -- 11, 12, 13, 14, 16,
-- -- 6, 7, 8, 9, 10,
-- -- 1, 2, 3, 4, 5,
-- #eval grid_bounds test_grid
-- #eval subgrid' test_grid ⟨⟨1, 1⟩, ⟨4, 3⟩, sorry⟩ sorry

end grid_instances