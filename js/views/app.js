var AppView = Backbone.View.extend({
	initialize: function () {
		this.template = _.template($('#tmpl_app').html());
		this.editor = new EditorView();
		this.inspector = new InspectorView();
		this.memview = new MemoryView();

		this.listenTo(Backbone.Events, 'app:redraw', this.redrawButtons);
		this.$('.download').addClass('disabled');
		
		this.render();
		editor = this.editor;
	},

	events: {
		'click .compile': 'compile',
		'click .reset': 'reset',
		'click .continue': 'continue',
		'click .step': 'step',
		'click .download': 'download'
	},

	render: function () {
		this.$el.empty().append(this.template());
		this.$('.editor').empty().append(this.editor.$el);
		this.$('.inspector').empty().append(this.inspector.$el);
		this.$('.memory').empty().append(this.memview.$el);
		this.redrawButtons();
	},

	compile: function () {
		var obj = ASSEMBLE(this.editor.getSource());
		console.log(obj);
		this.inspector.setObjectCode(obj);

		if (obj.errors.length === 0)
			INIT(obj.obj);

		Backbone.Events.trigger('app:redraw');
		this.$('.continue span').text('Start');
		this.$('.download').removeClass('disabled');
	},

	reset: function () {
			RESET();
			this.$('.continue span').text('Start');

			Backbone.Events.trigger('app:redraw');
	},

	continue: function () {
		if (IS_RUNNING()) {
			PAUSE();
		} else if (STAT === 'AOK' || STAT === 'DBG') {
			this.$('.continue span').text('Pause');
			this.$('.step').addClass('disabled');
			RUN(this.triggerRedraw);
		}
	},

	step: function () {
		if (!IS_RUNNING() && (STAT === 'AOK' || STAT === 'DBG')) {
			STEP();
			Backbone.Events.trigger('app:redraw');
		}
	},

	download: function () {
		var saveByteArray = (function () {
			var a = document.createElement("a");
			document.body.appendChild(a);
			a.style = "display: none";
			return function (data, name) {
				var blob = new Blob(data, {type: "octet/stream"}),
				    url = window.URL.createObjectURL(blob);
				a.href = url;
				a.download = name;
				a.click();
				window.URL.revokeObjectURL(url);
			};
		}());

		let MEMORY_COPY = [...MEMORY];
		while(MEMORY_COPY[MEMORY_COPY.length-1] === 0){
			MEMORY_COPY.pop();
		}
		MEMORY_COPY = new Uint8Array(MEMORY_COPY)
		
		saveByteArray([MEMORY_COPY], 'a.bin');
	},

	triggerRedraw: function () {
		Backbone.Events.trigger('app:redraw');
	},

	redrawButtons: function () {
		if (STAT === 'AOK' || STAT === 'DBG') {
			this.$('.continue span').text('Continue');
			this.$('.step, .continue').removeClass('disabled');
		} else {
			this.$('.step, .continue').addClass('disabled');
		}
	}
});
